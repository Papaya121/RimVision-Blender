bl_info = {"name": "RimVision Model Tools", "author": "RimVision", "version": (0, 4, 25),
           "blender": (4, 2, 0), "location": "View3D > Sidebar > RimVision", "category": "Import-Export"}

import importlib
import math
import queue
import re
import threading
import tempfile
import sys
import xml.etree.ElementTree as ET
from pathlib import Path

import bpy
import bpy.utils.previews
from bpy.props import BoolProperty, CollectionProperty, EnumProperty, FloatProperty, FloatVectorProperty, IntProperty, PointerProperty, StringProperty
from bpy_extras.io_utils import ImportHelper
for _module_name in ("addon", "catalog", "paths", "model", "sprites", "scene_tools"):
    _module = sys.modules.get(__name__ + "." + _module_name)
    if _module is not None:
        importlib.reload(_module)
from .catalog import active_mods, discover, load_snapshot, scan, sprite_folders
from .paths import find_installations
from .scene_tools import create_effect_marker, frame_model, image_for, import_model, material_preview, name_material, name_resource, object_surface, prepare_texture, refresh_model_textures, show_catalog_models, show_reference, sprite_path
from .sprites import cached_textures, extract
from .addon import add_dependency, create as create_addon, ensure_content, find_addons, read as read_addon, update_metadata, write_xml

_records = []
_previews = None
_mod_items = [("All", "Все моды", "")]
_model_items = {}
_empty_model_items = [("None", "Модели не найдены", "")]
_file_model_items = [("0", "Основная модель", "")]
_extracting = None
_loading = False
_known_meshes = {}
_pending_meshes = []
_directions = [(value, value, "") for value in ("Thing", "North", "East", "South", "West")]


def selection_record(settings):
    if 0 <= settings.index < len(settings.entries):
        index = settings.entries[settings.index].record_index
        if 0 <= index < len(_records):
            return _records[index]
    return None


def selected(context):
    return selection_record(context.scene.rimvision)


def model_root(obj):
    while obj.parent and obj.parent.get("rimvision_def") == obj.get("rimvision_def"):
        obj = obj.parent
    return obj


@bpy.app.handlers.persistent
def reset_mesh_tracking(*args):
    _pending_meshes.clear()
    _known_meshes.clear()
    for scene in bpy.data.scenes:
        _known_meshes[scene.as_pointer()] = (len(scene.objects), {obj.as_pointer() for obj in scene.objects if obj.type == "MESH"})


@bpy.app.handlers.persistent
def track_new_meshes(scene, depsgraph):
    previous = _known_meshes.get(scene.as_pointer())
    count = len(scene.objects)
    if previous is not None and previous[0] == count:
        return
    meshes = {obj.as_pointer(): obj for obj in scene.objects if obj.type == "MESH"}
    previous = previous[1] if previous is not None else set(meshes)
    _known_meshes[scene.as_pointer()] = (count, set(meshes))
    if _loading or scene != bpy.context.scene:
        return
    settings = scene.rimvision
    record = selection_record(settings)
    root = settings.current_model
    active = bpy.context.view_layer.objects.active
    if active and active.get("rimvision_def") and not active.get("rimvision_role"):
        root = model_root(active)
    if not settings.auto_attach_meshes or record is None or root is None or root.get("rimvision_def") != record["defName"]:
        return
    for pointer in meshes.keys() - previous:
        obj = meshes[pointer]
        if not obj.get("rimvision_def") and not obj.get("rimvision_role"):
            _pending_meshes.append((scene, obj, root))
    if _pending_meshes and not bpy.app.timers.is_registered(attach_new_meshes):
        bpy.app.timers.register(attach_new_meshes, first_interval=0.05)


def attach_new_meshes():
    if bpy.context.mode != "OBJECT":
        return 0.1 if _pending_meshes else None
    pending = list(_pending_meshes)
    _pending_meshes.clear()
    for scene, obj, root in pending:
        try:
            if scene != bpy.context.scene or not scene.rimvision.auto_attach_meshes or obj.get("rimvision_def") or obj.get("rimvision_role"):
                continue
            if scene.objects.get(obj.name) is None or scene.objects.get(root.name) is None:
                continue
            record = selected(bpy.context)
            if record is None or root.get("rimvision_def") != record["defName"] or obj.parent is not None:
                continue
            world = obj.matrix_world.copy()
            obj.parent = root
            obj.matrix_world = world
            for key in ("rimvision_def", "rimvision_filter", "rimvision_height_offset", "rimvision_source"):
                if key in root:
                    obj[key] = root[key]
            if not len(obj.data.materials):
                material = bpy.data.materials.new(obj.name + " surface")
                name_resource(material, record, "Материал")
                material.rimvision.use_uv = False
                obj.data.materials.append(material)
            attach_to_addon(bpy.context, obj)
            scene.rimvision.status = "Добавлено в модель: " + root.name
        except (ReferenceError, RuntimeError, ValueError) as error:
            print("[RimVision] Привязка меша: " + str(error))
    return None


def refresh(self, context):
    self.entries.clear()
    needle = self.search.casefold()
    for index, record in enumerate(_records):
        if needle not in " ".join(str(record.get(key, "")) for key in ("defName", "label", "mod", "packageId")).casefold():
            continue
        if self.category != "All" and record.get("category") != self.category:
            continue
        if self.mod_filter != "All" and record.get("packageId") != self.mod_filter:
            continue
        if self.models_only and not record.get("models"):
            continue
        if self.missing_models_only and record.get("models"):
            continue
        entry = self.entries.add()
        entry.name = record["defName"]
        entry.label = record.get("label", entry.name)
        entry.record_index = index
    self.index = 0
    record = selection_record(self)
    models = record.get("models", []) if record else []
    if models:
        defaults = [i for i, model in enumerate(models) if not model["filter"]]
        self.model_choice = str(defaults[-1] if defaults else len(models) - 1)


def ready_filter_changed(self, context):
    if self.models_only and self.missing_models_only:
        self.missing_models_only = False
        return
    refresh(self, context)


def missing_filter_changed(self, context):
    if self.missing_models_only and self.models_only:
        self.models_only = False
        return
    refresh(self, context)


def selection_changed(self, context):
    if _loading or not self.auto_reference or context is None or context.scene != self.id_data or self.workflow_stage in ("Setup", "Addons"):
        return
    record = selected(context)
    if record:
        try:
            show_reference(context.scene, record)
        except (OSError, RuntimeError, ValueError) as error:
            self.status = "Референс: " + str(error)


def reference_transform_changed(self, context):
    if _loading or context is None or context.scene != self.id_data:
        return
    if not self.auto_reference and (self.guides is None or not any(obj and obj.type == "EMPTY" and obj.get("rimvision_guide") for obj in self.guides.objects)):
        return
    record = selected(context)
    if record:
        try:
            show_reference(context.scene, record)
        except (OSError, RuntimeError, ValueError) as error:
            self.status = "Референс: " + str(error)


def index_changed(self, context):
    if not _loading and context and context.scene == self.id_data:
        record = selected(context)
        active = context.view_layer.objects.active
        if active and active.get("rimvision_def") and active["rimvision_def"] != (record["defName"] if record else "") and not active.hide_get(view_layer=context.view_layer):
            root = model_root(active)
            root["rimvision_filter"] = self.graphic_filter
            root["rimvision_height_offset"] = self.height_offset
        show_catalog_models(context, record)
        active = context.view_layer.objects.active
        self.current_model = model_root(active) if active and record and active.get("rimvision_def") == record["defName"] else None
        models = record.get("models", []) if record else []
        if models:
            defaults = [i for i, model in enumerate(models) if not model["filter"]]
            self.model_choice = str(defaults[-1] if defaults else len(models) - 1)
    selection_changed(self, context)


def model_items(self, context):
    record = selection_record(self)
    return _model_items.get(record["defName"] if record else "", _empty_model_items)


def cache_root():
    return Path(bpy.utils.user_resource("SCRIPTS", path="rimvision_cache", create=True))


def sprite_status_context(settings):
    try:
        config_time = Path(bpy.path.abspath(settings.config)).stat().st_mtime_ns if settings.config else 0
    except OSError:
        config_time = -1
    return repr((settings.game, settings.workshop, settings.config, settings.version, config_time))


def set_sprite_status(settings, textures, originals):
    settings.sprites_ready = bool(textures and originals)
    settings.sprite_count = len(textures) if settings.sprites_ready else 0
    settings.sprite_status_context = sprite_status_context(settings)


def refresh_sprite_status(settings):
    if not settings.game:
        set_sprite_status(settings, {}, {})
        return
    game = Path(bpy.path.abspath(settings.game))
    _, workshops, _ = find_installations(str(game))
    if settings.workshop:
        workshops.append(Path(bpy.path.abspath(settings.workshop)))
    mods, _ = discover(game, list(dict.fromkeys(workshops)))
    config = bpy.path.abspath(settings.config) if settings.config else None
    roots = sprite_folders(mods, settings.version, active_mods(config))
    set_sprite_status(settings, cached_textures(cache_root(), game, roots), cached_textures(cache_root(), game, roots, base=True))


def locate(settings):
    game, workshops, config = find_installations(bpy.path.abspath(settings.game) if settings.game else "")
    if game:
        settings.game = str(game)
    if workshops and not settings.workshop:
        settings.workshop = str(workshops[0])
    if config and not settings.config:
        settings.config = str(config)
    return game


def preview_icon(record):
    path = record.get("previewSprite") or sprite_path(record, "Thing") or sprite_path(record, "South")
    if not path:
        return 0
    try:
        if path not in _previews:
            _previews.load(path, path, "IMAGE")
        return _previews[path].icon_id
    except (OSError, RuntimeError, KeyError):
        return 0


class RVEntry(bpy.types.PropertyGroup):
    label: StringProperty()
    record_index: IntProperty()


class RVAddonModel(bpy.types.PropertyGroup):
    definition: StringProperty()
    file: StringProperty()
    index: IntProperty()
    graphic_filter: StringProperty()


class RVFoundAddon(bpy.types.PropertyGroup):
    path: StringProperty(subtype="DIR_PATH")
    package: StringProperty()
    count: IntProperty()
    state: StringProperty()
    origin: StringProperty()


def effect_changed(self, context):
    obj = self.id_data
    if obj.type == "LIGHT" and self.kind == "light":
        obj.data.color = self.color
        obj.data.energy = self.intensity * 100
        obj.data.use_custom_distance = True
        obj.data.cutoff_distance = self.radius


class RVEffectSettings(bpy.types.PropertyGroup):
    kind: EnumProperty(items=[("None", "Нет", ""), ("fire", "Огонь", ""), ("light", "Свет", "")], default="None", update=effect_changed)
    size: FloatProperty(name="Размер огня", default=1, min=0.05, max=5)
    radius: FloatProperty(name="Визуальный радиус света", default=8, min=0.1, max=32, update=effect_changed)
    intensity: FloatProperty(name="Яркость", default=1, min=0, max=8, update=effect_changed)
    color: FloatVectorProperty(name="Оттенок игрового света", subtype="COLOR", size=3, min=0, max=1, default=(1, 1, 1), update=effect_changed)
    always: BoolProperty(name="Декоративный огонь — горит всегда", default=False)


class RVSettings(bpy.types.PropertyGroup):
    workflow_stage: EnumProperty(items=[("Auto", "Автоматически", ""), ("Setup", "Подготовка", ""), ("Addons", "Выбор аддона", ""), ("Ready", "Работа", "")], default="Auto")
    game: StringProperty(name="RimWorld folder", subtype="DIR_PATH")
    workshop: StringProperty(name="Workshop 294100 folder", subtype="DIR_PATH")
    model_root: StringProperty(name="Папка мода с моделями", description="Необязательная рабочая копия мода с папкой OptionalContent; её модели имеют приоритет", subtype="DIR_PATH")
    version: StringProperty(name="RimWorld version", default="1.6")
    snapshot: StringProperty(name="Loaded catalog JSON", subtype="FILE_PATH")
    config: StringProperty(name="ModsConfig.xml", subtype="FILE_PATH")
    active_only: BoolProperty(name="Только активные моды", default=False)
    advanced: BoolProperty(name="Пути и дополнительные настройки")
    surface_options: BoolProperty(name="Настройки активного материала")
    addon_options: BoolProperty(name="Аддон")
    setup_options: BoolProperty(name="Игра и пути")
    catalog_options: BoolProperty(name="Каталог")
    model_options: BoolProperty(name="Текущая модель")
    reference_options: BoolProperty(name="Референс")
    effect_options: BoolProperty(name="Огонь и свет")
    export_options: BoolProperty(name="Сохранение и экспорт")
    mod_filter: EnumProperty(name="Мод", items=lambda self, context: _mod_items, update=refresh)
    models_only: BoolProperty(name="Только с готовой моделью", update=ready_filter_changed)
    missing_models_only: BoolProperty(name="Только без готовой модели", update=missing_filter_changed)
    model_choice: EnumProperty(name="Модель", items=model_items)
    reference_direction: EnumProperty(name="Направление референса", items=_directions, default="South", update=selection_changed)
    reference_all_sides: BoolProperty(name="Все доступные стороны", default=True, update=reference_transform_changed)
    reference_opacity: FloatProperty(name="Прозрачность референса", min=0.05, max=1, default=0.8, update=selection_changed)
    reference_side: EnumProperty(name="Сторона размещения", items=[("Right", "Справа (+X)", ""), ("Left", "Слева (−X)", ""),
        ("North", "Север (+Y)", ""), ("South", "Юг (−Y)", ""), ("Above", "Сверху (+Z)", ""), ("Below", "Снизу (−Z)", "")], default="Right", update=reference_transform_changed)
    reference_gap: FloatProperty(name="Отступ от модели", default=0.5, min=0, update=reference_transform_changed)
    reference_offset: FloatVectorProperty(name="Дополнительное смещение", size=3, subtype="TRANSLATION", default=(0, 0, 0), update=reference_transform_changed)
    reference_rotation: FloatVectorProperty(name="Поворот", size=3, subtype="EULER", unit="ROTATION", default=(math.pi / 2, 0, -math.pi / 2), update=reference_transform_changed)
    auto_reference: BoolProperty(name="Референс при выборе предмета", default=True, update=selection_changed)
    guides: PointerProperty(type=bpy.types.Collection)
    output: StringProperty(name="Output mod folder", subtype="DIR_PATH")
    addon_path: StringProperty(subtype="DIR_PATH")
    addon_name: StringProperty()
    found_addons: CollectionProperty(type=RVFoundAddon)
    found_addon_index: IntProperty()
    addon_discovery_status: StringProperty(default="Аддоны ещё не найдены")
    addon_edit_name: StringProperty(name="Название мода")
    addon_description: PointerProperty(type=bpy.types.Text)
    addon_preview: StringProperty(name="Превью", subtype="FILE_PATH")
    addon_metadata_options: BoolProperty(name="Название, описание и превью")
    addon_models: CollectionProperty(type=RVAddonModel)
    addon_index: IntProperty()
    addon_collection: PointerProperty(type=bpy.types.Collection)
    current_model: PointerProperty(type=bpy.types.Object)
    auto_attach_meshes: BoolProperty(name="Привязывать новые меши из Shift+A", default=True)
    search: StringProperty(name="Search (name / mod)", update=refresh)
    category: EnumProperty(name="Category", items=[(v, v, "") for v in ("All", "Building", "Item", "Plant", "Pawn")], default="All", update=refresh)
    entries: CollectionProperty(type=RVEntry)
    index: IntProperty(update=index_changed)
    status: StringProperty(default="Найдите игру и загрузите каталог")
    sprites_ready: BoolProperty(options={"SKIP_SAVE"})
    sprite_count: IntProperty(options={"SKIP_SAVE"})
    sprite_status_context: StringProperty(options={"SKIP_SAVE"})
    graphic_filter: StringProperty(name="Graphic path filter")
    height_offset: FloatProperty(name="Height offset", default=0)
    overwrite: BoolProperty(name="Replace existing model file", default=False)


class RVSurface(bpy.types.PropertyGroup):
    mode: EnumProperty(name="Surface", items=[("Game", "Game texture", ""), ("Solid", "Solid color", ""), ("Custom", "Своя текстура", ""), ("Object", "Материал объекта", "Брать цвет и текстуру из назначенного материала Blender"), ("Atlas", "Атлас всех ракурсов", "Объединить игровые спрайты в одну текстуру 2×2 для UV-развёртки")], default="Game")
    texture_path: StringProperty(name="Файл текстуры", subtype="FILE_PATH")
    direction: EnumProperty(name="Texture direction", items=_directions, default="Thing")
    color: FloatVectorProperty(name="Color", subtype="COLOR", size=3, min=0, max=1, default=(0.5, 0.5, 0.5))
    tint: BoolProperty(name="Tint with thing color")
    two_sided: BoolProperty(name="Two sided", default=True)
    turret_top: BoolProperty(name="Turret top")
    required_links: StringProperty(name="Required links")
    forbidden_links: StringProperty(name="Forbidden links")
    use_uv: BoolProperty(name="Export active UV map", default=True)


class RV_UL_catalog(bpy.types.UIList):
    def draw_item(self, context, layout, data, item, icon, active_data, active_propname, index):
        record = _records[item.record_index] if item.record_index < len(_records) else {}
        icon_id = preview_icon(record) if record else 0
        row = layout.row()
        if icon_id:
            row.label(text=item.label, icon_value=icon_id)
        else:
            row.label(text=item.label, icon="MESH_CUBE")
        row.label(text=item.name)
        if record.get("builtin3dLocked") or record.get("door"):
            row.label(text="3D • замена недоступна", icon="LOCKED")
        elif record.get("models"):
            row.label(text="Кастомная 3D", icon="CHECKMARK")
        elif record.get("builtin3d") or record.get("defName") == "Wall":
            row.label(text="Встроенная 3D", icon="MESH_CUBE")


class RVLoad(bpy.types.Operator):
    bl_idname = "rimvision.load_catalog"
    bl_label = "Load catalog"
    source: EnumProperty(items=[("Files", "Files", ""), ("Snapshot", "Snapshot", "")])

    def execute(self, context):
        global _records, _mod_items, _model_items, _loading
        settings = context.scene.rimvision
        try:
            if self.source == "Snapshot":
                if not settings.snapshot:
                    raise ValueError("Select a JSON catalog")
                records = load_snapshot(bpy.path.abspath(settings.snapshot))
                status = "Loaded definitions: " + str(len(records))
            else:
                if not settings.game:
                    locate(settings)
                if not settings.game:
                    raise ValueError("Игра не найдена. Укажите папку RimWorld в настройках путей.")
                game = Path(bpy.path.abspath(settings.game))
                _, auto_workshops, _ = find_installations(str(game))
                workshop = list(dict.fromkeys([*auto_workshops, *([Path(bpy.path.abspath(settings.workshop))] if settings.workshop else [])]))
                config = bpy.path.abspath(settings.config) if settings.config else None
                mods, _ = discover(game, workshop)
                roots = sprite_folders(mods, settings.version, active_mods(config))
                textures = cached_textures(cache_root(), game, roots)
                originals = cached_textures(cache_root(), game, roots, base=True)
                set_sprite_status(settings, textures, originals)
                records, warnings = scan(game, workshop, settings.version, textures,
                                         config, settings.active_only,
                                         bpy.path.abspath(settings.model_root) if settings.model_root else None,
                                         base_cached=originals,
                                         supplemental_cached=cached_textures(cache_root(), game, roots, supplemental=True))
                status = str(len(records)) + " объектов • " + str(sum(bool(r.get("models")) for r in records)) + " с моделями • XML-патчи не применяются"
                for warning in warnings:
                    print("[RimVision] " + warning)
            _records = records
            mods = {r.get("packageId", ""): r.get("mod", "") for r in records}
            _mod_items = [("All", "Все моды", "")] + [(package, name or package, package) for package, name in sorted(mods.items(), key=lambda p: p[1].casefold()) if package]
            _model_items = {r["defName"]: [(str(i), (m["filter"] or "Основная") + " • " + m["mod"], m["file"], i) for i, m in enumerate(r.get("models", []))] for r in records if r.get("models")}
            _previews.clear()
            _loading = True
            try:
                for scene in bpy.data.scenes:
                    scene.rimvision.mod_filter = "All"
                    refresh(scene.rimvision, context)
                    scene.rimvision.status = status
                    refresh_model_textures(scene, records)
            finally:
                _loading = False
            index_changed(settings, context)
            try:
                refresh_found_addons(settings)
            except (OSError, ValueError, ET.ParseError, RuntimeError) as error:
                settings.addon_discovery_status = str(error)
            if settings.workflow_stage == "Setup" and _records and settings.sprites_ready and settings.sprite_status_context == sprite_status_context(settings):
                settings.workflow_stage = "Addons"
        except (OSError, ValueError, KeyError, ET.ParseError, TypeError, RuntimeError) as error:
            self.report({"ERROR"}, str(error))
            return {"CANCELLED"}
        return {"FINISHED"}


class RVFind(bpy.types.Operator):
    bl_idname = "rimvision.find_game"
    bl_label = "Найти игру и загрузить каталог"

    def execute(self, context):
        if not locate(context.scene.rimvision):
            context.scene.rimvision.advanced = True
            self.report({"ERROR"}, "RimWorld не найден в Steam-библиотеках; укажите папку вручную")
            return {"CANCELLED"}
        try:
            return bpy.ops.rimvision.load_catalog(source="Files")
        except RuntimeError as error:
            self.report({"ERROR"}, str(error))
            return {"CANCELLED"}


class RVPrepareSprites(bpy.types.Operator):
    bl_idname = "rimvision.prepare_sprites"
    bl_label = "Подготовить спрайты игры"
    _timer = None

    def execute(self, context):
        global _extracting
        if _extracting:
            self.report({"WARNING"}, "Извлечение уже выполняется")
            return {"CANCELLED"}
        settings = context.scene.rimvision
        if not settings.game:
            locate(settings)
        if not settings.game:
            self.report({"ERROR"}, "Сначала найдите папку игры")
            return {"CANCELLED"}
        game = bpy.path.abspath(settings.game)
        _, workshops, _ = find_installations(game)
        if settings.workshop:
            workshops.append(Path(bpy.path.abspath(settings.workshop)))
        try:
            mods, _ = discover(Path(game), list(dict.fromkeys(workshops)))
            config = bpy.path.abspath(settings.config) if settings.config else None
            active = active_mods(config)
            roots = sprite_folders(mods, settings.version, active)
            extra_roots = [root for root in sprite_folders(mods, settings.version, active, include_inactive=True) if root not in roots]
        except (OSError, ValueError, ET.ParseError) as error:
            self.report({"ERROR"}, str(error))
            return {"CANCELLED"}
        cache = cache_root()
        self._messages = queue.Queue()
        self._cancelled = threading.Event()
        self._scene = context.scene
        self._game = game
        messages, cancelled = self._messages, self._cancelled

        def worker():
            try:
                textures, errors = extract(cache, game, roots, lambda message: messages.put(("status", message)), cancelled, extra_roots)
                messages.put(("done", (len(textures), errors)))
            except Exception as error:
                messages.put(("error", str(error)))

        threading.Thread(target=worker, daemon=True).start()
        _extracting = self
        self._timer = context.window_manager.event_timer_add(0.2, window=context.window)
        context.window_manager.modal_handler_add(self)
        settings.status = "Извлечение спрайтов… Esc — отмена"
        return {"RUNNING_MODAL"}

    def cancel(self, context):
        global _extracting
        self._cancelled.set()
        if self._timer:
            context.window_manager.event_timer_remove(self._timer)
            self._timer = None
        _extracting = None

    def modal(self, context, event):
        if event.type == "ESC":
            self._cancelled.set()
            self._scene.rimvision.status = "Отмена извлечения…"
        if event.type != "TIMER":
            return {"PASS_THROUGH"}
        while not self._messages.empty():
            kind, value = self._messages.get_nowait()
            if kind == "status":
                self._scene.rimvision.status = "Спрайты: " + value
            else:
                cancelled = self._cancelled.is_set()
                self.cancel(context)
                if kind == "error":
                    self.report({"ERROR"}, value)
                    self._scene.rimvision.status = value
                    return {"CANCELLED"}
                for error in value[1]:
                    print("[RimVision] " + error)
                if not cancelled and self._scene == context.scene and bpy.path.abspath(context.scene.rimvision.game) == self._game:
                    bpy.ops.rimvision.load_catalog(source="Files")
                self.report({"INFO"}, ("Извлечение отменено. " if cancelled else "") + "Спрайтов в кэше: " + str(value[0]))
                return {"FINISHED"}
        if context.area:
            context.area.tag_redraw()
        return {"PASS_THROUGH"}


class RVReference(bpy.types.Operator):
    bl_idname = "rimvision.show_reference"
    bl_label = "Показать референс и сетку клеток"
    bl_options = {"REGISTER", "UNDO"}

    def execute(self, context):
        record = selected(context)
        if record is None:
            return {"CANCELLED"}
        try:
            show_reference(context.scene, record)
        except (OSError, RuntimeError, ValueError) as error:
            self.report({"ERROR"}, str(error))
            return {"CANCELLED"}
        return {"FINISHED"}


class RVImport(bpy.types.Operator):
    bl_idname = "rimvision.import_model"
    bl_label = "Добавить готовую модель в сцену"
    bl_options = {"REGISTER", "UNDO"}

    def execute(self, context):
        record = selected(context)
        try:
            if context.mode != "OBJECT" or record is None:
                raise ValueError("Выберите предмет в Object Mode")
            models = record.get("models", [])
            index = int(context.scene.rimvision.model_choice)
            source = models[index]
            obj = import_model(context, record, source["file"], source["index"])
            attach_to_addon(context, obj)
        except (OSError, RuntimeError, ValueError, IndexError, ET.ParseError) as error:
            self.report({"ERROR"}, str(error))
            return {"CANCELLED"}
        return {"FINISHED"}


class RVImportFile(bpy.types.Operator, ImportHelper):
    bl_idname = "rimvision.import_model_file"
    bl_label = "Открыть XML-модель…"
    bl_options = {"REGISTER", "UNDO"}
    filename_ext = ".xml"
    filter_glob: StringProperty(default="*.xml", options={"HIDDEN"})
    variant: EnumProperty(name="Вариант модели", items=lambda self, context: _file_model_items)
    pick_variant: BoolProperty(default=False, options={"HIDDEN", "SKIP_SAVE"})

    def draw(self, context):
        self.layout.prop(self, "variant")

    def execute(self, context):
        global _file_model_items
        record = selected(context)
        try:
            if context.mode != "OBJECT" or record is None:
                raise ValueError("Сначала выберите предмет каталога в Object Mode")
            nodes = list(ET.parse(self.filepath).getroot())
            candidates = [i for i, node in enumerate(nodes) if node.findtext("thingDef", "").strip() == record["defName"]]
            if not candidates:
                raise ValueError("В XML нет модели для " + record["defName"])
            if len(candidates) > 1 and not self.pick_variant:
                _file_model_items = [(str(i), nodes[i].findtext("graphicPathContains") or "Основная модель", str(i), i) for i in candidates]
                self.variant = str(candidates[0])
                self.pick_variant = True
                return context.window_manager.invoke_props_dialog(self)
            index = int(self.variant) if self.pick_variant else candidates[0]
            obj = import_model(context, record, self.filepath, index)
            attach_to_addon(context, obj)
        except (OSError, RuntimeError, ValueError, ET.ParseError) as error:
            self.report({"ERROR"}, str(error))
            return {"CANCELLED"}
        return {"FINISHED"}


class RVTemplate(bpy.types.Operator):
    bl_idname = "rimvision.create_template"
    bl_label = "Добавить модель в сцену"
    bl_options = {"REGISTER", "UNDO"}
    force_new: BoolProperty(default=False, options={"HIDDEN", "SKIP_SAVE"})
    primitive: EnumProperty(name="Начальная форма", items=[("Cube", "Куб", ""), ("Cylinder", "Цилиндр", ""),
        ("Cone", "Конус", ""), ("Sphere", "UV-сфера", ""), ("Icosphere", "Икосфера", ""),
        ("Plane", "Плоскость", ""), ("Torus", "Тор", "")], default="Cube")

    def invoke(self, context, event):
        record = selected(context)
        if record is None or context.mode != "OBJECT" or (record.get("models") and not self.force_new):
            return self.execute(context)
        return context.window_manager.invoke_props_dialog(self)

    def draw(self, context):
        self.layout.prop(self, "primitive")

    def execute(self, context):
        record = selected(context)
        if record is None:
            return {"CANCELLED"}
        if context.mode != "OBJECT":
            self.report({"ERROR"}, "Перейдите в Object Mode")
            return {"CANCELLED"}
        if record.get("models") and not self.force_new:
            return RVImport.execute(self, context)
        primitive, options = {
            "Cube": (bpy.ops.mesh.primitive_cube_add, {"size": 1}),
            "Cylinder": (bpy.ops.mesh.primitive_cylinder_add, {"radius": 0.5, "depth": 1}),
            "Cone": (bpy.ops.mesh.primitive_cone_add, {"radius1": 0.5, "radius2": 0, "depth": 1}),
            "Sphere": (bpy.ops.mesh.primitive_uv_sphere_add, {"radius": 0.5}),
            "Icosphere": (bpy.ops.mesh.primitive_ico_sphere_add, {"radius": 0.5}),
            "Plane": (bpy.ops.mesh.primitive_plane_add, {"size": 1}),
            "Torus": (bpy.ops.mesh.primitive_torus_add, {"mode": "MAJOR_MINOR", "major_radius": 0.35, "minor_radius": 0.15}),
        }[self.primitive]
        primitive(align="WORLD", location=(0, 0, 0), rotation=(0, 0, 0), **options)
        obj = context.object
        obj.name = record["defName"]
        if self.primitive == "Cube":
            obj.scale = (record["width"], record["depth"], 1)
        else:
            points = [vertex.co for vertex in obj.data.vertices]
            width = max(point.x for point in points) - min(point.x for point in points)
            depth = max(point.y for point in points) - min(point.y for point in points)
            scale = min(record["width"] / width, record["depth"] / depth)
            obj.scale = (scale, scale, scale)
        obj.location.z = -min(vertex.co.z for vertex in obj.data.vertices) * obj.scale.z
        material = bpy.data.materials.new(record["defName"] + " surface")
        name_resource(material, record, "Материал")
        material.rimvision.use_uv = False
        obj.data.materials.append(material)
        obj["rimvision_def"] = record["defName"]
        context.scene.rimvision.graphic_filter = ""
        context.scene.rimvision.height_offset = 0
        obj["rimvision_filter"] = ""
        obj["rimvision_height_offset"] = 0.0
        attach_to_addon(context, obj)
        show_reference(context.scene, record)
        frame_model(context, record, obj)
        return {"FINISHED"}


class RVTexture(bpy.types.Operator):
    bl_idname = "rimvision.use_sprite"
    bl_label = "Назначить игровой спрайт"
    bl_options = {"REGISTER", "UNDO"}

    def execute(self, context):
        record = selected(context)
        obj = context.object
        if record is None or obj is None or obj.type != "MESH" or context.mode != "OBJECT":
            self.report({"ERROR"}, "Select a catalog entry and a mesh in Object Mode")
            return {"CANCELLED"}
        direction = obj.active_material.rimvision.direction if obj.active_material else "Thing"
        path = sprite_path(record, direction)
        if not path or not Path(path).is_file():
            self.report({"ERROR"}, "Спрайт недоступен. Нажмите «Подготовить спрайты игры».")
            return {"CANCELLED"}
        try:
            image = image_for(record, direction)
        except RuntimeError as error:
            self.report({"ERROR"}, str(error))
            return {"CANCELLED"}
        material = obj.active_material
        if material is None or material.get("rimvision_auto_name") is None or material.users > 1 or material.rimvision.mode != "Game":
            material = bpy.data.materials.new(record["defName"] + " game texture")
            name_resource(material, record, "Материал")
        else:
            material.rimvision.mode = "Game"
            material.rimvision.use_uv = True
        material.rimvision.direction = direction
        material_preview(material, record)
        if len(obj.data.materials):
            obj.data.materials[obj.active_material_index] = material
        else:
            obj.data.materials.append(material)
        self.report({"INFO"}, "Game sprite assigned to the active material slot")
        return {"FINISHED"}


def number(value):
    if not math.isfinite(value):
        raise ValueError("Non-finite coordinate")
    return format(value, ".9g")


def field(node, name, value):
    ET.SubElement(node, name).text = str(value)


def refresh_found_addons(settings):
    previous = settings.found_addons[settings.found_addon_index].path if 0 <= settings.found_addon_index < len(settings.found_addons) else settings.addon_path
    game = locate(settings)
    _, workshops, _ = find_installations(str(game) if game else "")
    if settings.workshop:
        workshops.append(Path(bpy.path.abspath(settings.workshop)))
    workshops = [root for root in dict.fromkeys(workshops) if root.is_dir()]
    roots = [root for root, _, _ in discover(game, workshops)[0]] if game else [root for workshop in workshops for root in workshop.iterdir() if root.is_dir()]
    local = bpy.utils.user_resource("SCRIPTS", path="rimvision_addons", create=False)
    if local and Path(local).is_dir():
        roots.extend(root for root in Path(local).iterdir() if root.is_dir())
    roots.extend(Path(bpy.path.abspath(path)) for path in (settings.addon_path, settings.model_root) if path)
    found, warnings = find_addons(roots)
    active = active_mods(bpy.path.abspath(settings.config) if settings.config else None)
    settings.found_addons.clear()
    for addon in found:
        entry = settings.found_addons.add()
        entry.name, entry.path, entry.package, entry.count = addon["name"], addon["path"], addon["package"], addon["count"]
        entry.state = "Статус неизвестен" if active is None else "Включён" if entry.package.lower() in active else "Выключен"
        entry.origin = "Workshop" if any(Path(entry.path).is_relative_to(root.resolve()) for root in workshops) else "Папка мода"
    settings.found_addon_index = next((i for i, entry in enumerate(settings.found_addons) if entry.path.casefold() == previous.casefold()), 0)
    settings.addon_discovery_status = "Найдено аддонов: " + str(len(found)) + (" • ошибок: " + str(len(warnings)) if warnings else "")
    for warning in warnings:
        print("[RimVision] " + warning)


def refresh_addon(settings):
    name, models = read_addon(bpy.path.abspath(settings.addon_path))
    settings.addon_name = name
    settings.addon_models.clear()
    for model in models:
        entry = settings.addon_models.add()
        entry.name = model["definition"] + (" • " + model["filter"] if model["filter"] else "")
        entry.definition = model["definition"]
        entry.file = model["file"]
        entry.index = model["index"]
        entry.graphic_filter = model["filter"]
    settings.addon_index = min(settings.addon_index, max(len(models) - 1, 0))


def open_addon(context, root):
    settings = context.scene.rimvision
    name, _ = read_addon(root)
    root = str(Path(root).resolve())
    add_dependency(root, "papaya.rimvision", "RimVision")
    ensure_content(root)
    collection = next((c for c in context.scene.collection.children if c.get("rimvision_addon") == root), None)
    if collection is None:
        collection = bpy.data.collections.new(name)
        context.scene.collection.children.link(collection)
        collection["rimvision_addon"] = root
    settings.addon_path = settings.output = root
    settings.addon_collection = collection
    if any((Path(root) / "OptionalContent" / n / "Models").is_dir() for n in ("RimVision", "RimWorld3DVR")):
        settings.model_root = root
    else:
        settings.model_root = ""
    refresh_addon(settings)
    load_addon_metadata(settings)
    if settings.workflow_stage in ("Setup", "Addons"):
        settings.workflow_stage = "Ready"
        settings.catalog_options = True
        settings.model_options = True
        settings.addon_options = False


def load_addon_metadata(settings):
    root = str(Path(bpy.path.abspath(settings.addon_path)).resolve())
    about = ET.parse(Path(root) / "About/About.xml").getroot()
    name = about.findtext("name", Path(root).name)
    settings.addon_edit_name = name
    description = next((text for text in bpy.data.texts if text.get("rimvision_addon") == root), None)
    if description is None:
        description = bpy.data.texts.new(name + " — описание")
        description["rimvision_addon"] = root
    description.from_string(about.findtext("description", ""))
    settings.addon_description = description
    preview = Path(root) / "About/Preview.png"
    settings.addon_preview = str(preview) if preview.is_file() else ""


def attach_to_addon(context, obj):
    settings = context.scene.rimvision
    record = selected(context)
    if record and obj.get("rimvision_def") == record["defName"]:
        settings.current_model = model_root(obj)
    if not settings.addon_path or settings.addon_collection is None:
        show_catalog_models(context, selected(context))
        return
    collection = settings.addon_collection
    for member in (obj, *obj.children_recursive):
        if collection.objects.get(member.name) is None:
            collection.objects.link(member)
        for old in list(member.users_collection):
            if old != collection:
                old.objects.unlink(member)
    show_catalog_models(context, selected(context))


class RVEditAddonDescription(bpy.types.Operator):
    bl_idname = "rimvision.edit_addon_description"
    bl_label = "Редактировать описание"

    def execute(self, context):
        description = context.scene.rimvision.addon_description
        if description is None and context.scene.rimvision.addon_path:
            try:
                load_addon_metadata(context.scene.rimvision)
                description = context.scene.rimvision.addon_description
            except (OSError, ValueError, ET.ParseError, RuntimeError) as error:
                self.report({"ERROR"}, str(error))
                return {"CANCELLED"}
        if description is None or context.area is None:
            return {"CANCELLED"}
        existing = next((area for area in context.screen.areas if area.type == "TEXT_EDITOR" and area.spaces.active.text == description), None)
        if existing is None:
            before = {area.as_pointer() for area in context.screen.areas}
            try:
                region = next(region for region in context.area.regions if region.type == "WINDOW")
                with context.temp_override(area=context.area, region=region):
                    result = bpy.ops.screen.area_split(direction="HORIZONTAL", factor=0.65)
                existing = next((area for area in context.screen.areas if area.as_pointer() not in before), None)
                if result != {"FINISHED"} or existing is None:
                    self.report({"ERROR"}, "Не удалось открыть редактор описания")
                    return {"CANCELLED"}
                existing.type = "TEXT_EDITOR"
            except RuntimeError as error:
                self.report({"ERROR"}, str(error))
                return {"CANCELLED"}
        existing.spaces.active.text = description
        existing.spaces.active.show_word_wrap = True
        return {"FINISHED"}


class RVSaveAddonMetadata(bpy.types.Operator):
    bl_idname = "rimvision.save_addon_metadata"
    bl_label = "Сохранить оформление аддона"

    def execute(self, context):
        settings = context.scene.rimvision
        image = temporary = None
        try:
            if not settings.addon_path or not settings.addon_edit_name.strip():
                raise ValueError("Откройте аддон и введите его название")
            root = Path(bpy.path.abspath(settings.addon_path))
            read_addon(root)
            destination = root / "About/Preview.png"
            if settings.addon_preview:
                source = Path(bpy.path.abspath(settings.addon_preview)).resolve()
                if not source.is_file():
                    raise ValueError("Файл превью не найден")
                if source != destination.resolve():
                    image = bpy.data.images.load(str(source), check_existing=False)
                    if image.size[0] <= 0 or image.size[1] <= 0:
                        raise ValueError("Не удалось прочитать изображение превью")
                    with tempfile.NamedTemporaryFile(dir=destination.parent, suffix=".png", delete=False) as output:
                        temporary = Path(output.name)
                    image.file_format = "PNG"
                    image.filepath_raw = str(temporary)
                    image.save()
            description = settings.addon_description.as_string() if settings.addon_description else ET.parse(root / "About/About.xml").getroot().findtext("description", "")
            update_metadata(root, settings.addon_edit_name, description)
            if temporary:
                temporary.replace(destination)
            if destination.is_file():
                settings.addon_preview = str(destination)
                if str(destination) in _previews:
                    del _previews[str(destination)]
            ensure_content(root)
            refresh_addon(settings)
            settings.addon_edit_name = settings.addon_name
            if settings.addon_collection:
                settings.addon_collection.name = settings.addon_name
            if settings.addon_description:
                settings.addon_description.name = settings.addon_name + " — описание"
            self.report({"INFO"}, "Название, описание и превью сохранены")
        except (OSError, RuntimeError, ValueError, ET.ParseError) as error:
            self.report({"ERROR"}, str(error))
            return {"CANCELLED"}
        finally:
            if image:
                bpy.data.images.remove(image)
            if temporary:
                temporary.unlink(missing_ok=True)
        return {"FINISHED"}


class RVCreateAddon(bpy.types.Operator):
    bl_idname = "rimvision.create_addon"
    bl_label = "Создать аддон"
    name: StringProperty(name="Название")

    def invoke(self, context, event):
        return context.window_manager.invoke_props_dialog(self)

    def draw(self, context):
        self.layout.prop(self, "name")

    def execute(self, context):
        settings = context.scene.rimvision
        try:
            game = locate(settings)
            parent = game / "Mods" if game else Path(bpy.utils.user_resource("SCRIPTS", path="rimvision_addons", create=True))
            root = create_addon(parent, self.name, settings.version)
            open_addon(context, root)
            try:
                refresh_found_addons(settings)
            except (OSError, ValueError, ET.ParseError, RuntimeError) as error:
                settings.addon_discovery_status = str(error)
            settings.status = "Создан аддон: " + settings.addon_name
            self.report({"INFO"}, "Аддон создан: " + str(root))
        except (OSError, ValueError, ET.ParseError, RuntimeError) as error:
            self.report({"ERROR"}, str(error))
            return {"CANCELLED"}
        return {"FINISHED"}


class RV_UL_found_addons(bpy.types.UIList):
    def draw_item(self, context, layout, data, item, icon, active_data, active_propname, index):
        row = layout.row()
        row.label(text=item.name, icon="OUTLINER_COLLECTION")
        row.label(text=str(item.count) + " моделей")
        row.label(text=item.state)


class RVFindAddons(bpy.types.Operator):
    bl_idname = "rimvision.find_addons"
    bl_label = "Найти аддоны"

    def execute(self, context):
        try:
            refresh_found_addons(context.scene.rimvision)
        except (OSError, ValueError, ET.ParseError, RuntimeError) as error:
            self.report({"ERROR"}, str(error))
            return {"CANCELLED"}
        return {"FINISHED"}


class RVOpenFoundAddon(bpy.types.Operator):
    bl_idname = "rimvision.open_found_addon"
    bl_label = "Открыть выбранный аддон"

    def execute(self, context):
        settings = context.scene.rimvision
        if not 0 <= settings.found_addon_index < len(settings.found_addons):
            self.report({"ERROR"}, "Выберите аддон в списке")
            return {"CANCELLED"}
        return bpy.ops.rimvision.open_addon(directory=settings.found_addons[settings.found_addon_index].path)


class RVOpenAddon(bpy.types.Operator):
    bl_idname = "rimvision.open_addon"
    bl_label = "Открыть аддон"
    directory: StringProperty(subtype="DIR_PATH")
    filter_folder: BoolProperty(default=True, options={"HIDDEN"})

    def invoke(self, context, event):
        settings = context.scene.rimvision
        game = Path(bpy.path.abspath(settings.game)) if settings.game else locate(settings)
        if game and (game / "Mods").is_dir():
            self.directory = (game / "Mods").resolve().as_posix() + "/"
        context.window_manager.fileselect_add(self)
        return {"RUNNING_MODAL"}

    def execute(self, context):
        try:
            open_addon(context, bpy.path.abspath(self.directory))
            if context.scene.rimvision.game:
                bpy.ops.rimvision.load_catalog(source="Files")
            else:
                refresh_found_addons(context.scene.rimvision)
        except (OSError, ValueError, ET.ParseError, RuntimeError) as error:
            self.report({"ERROR"}, str(error))
            return {"CANCELLED"}
        return {"FINISHED"}


class RVRefreshAddon(bpy.types.Operator):
    bl_idname = "rimvision.refresh_addon"
    bl_label = "Обновить список моделей аддона"

    def execute(self, context):
        try:
            refresh_addon(context.scene.rimvision)
        except (OSError, ValueError, ET.ParseError) as error:
            self.report({"ERROR"}, str(error))
            return {"CANCELLED"}
        return {"FINISHED"}


class RVLoadAddonModel(bpy.types.Operator):
    bl_idname = "rimvision.load_addon_model"
    bl_label = "Загрузить модель аддона"
    bl_options = {"REGISTER", "UNDO"}

    def execute(self, context):
        settings = context.scene.rimvision
        try:
            if context.mode != "OBJECT" or not 0 <= settings.addon_index < len(settings.addon_models):
                raise ValueError("Выберите модель в Object Mode")
            entry = settings.addon_models[settings.addon_index]
            record = next((r for r in _records if r["defName"] == entry.definition), None)
            if record is None:
                raise ValueError("Загрузите каталог игры с модом, определяющим " + entry.definition)
            settings.search = entry.definition
            settings.mod_filter = "All"
            settings.category = "All"
            settings.models_only = False
            settings.missing_models_only = False
            settings.index = next(i for i, item in enumerate(settings.entries) if _records[item.record_index] is record)
            obj = import_model(context, record, entry.file, entry.index)
            attach_to_addon(context, obj)
        except (OSError, ValueError, RuntimeError, ET.ParseError, StopIteration) as error:
            self.report({"ERROR"}, str(error))
            return {"CANCELLED"}
        return {"FINISHED"}


class RV_UL_addon(bpy.types.UIList):
    def draw_item(self, context, layout, data, item, icon, active_data, active_propname, index):
        layout.label(text=item.name, icon="MESH_DATA")


class RVExport(bpy.types.Operator):
    bl_idname = "rimvision.export_model"
    bl_label = "Экспортировать модель"

    def execute(self, context):
        return self._export(context)

    def _export(self, context, record=None, objects=None):
        if _pending_meshes:
            attach_new_meshes()
        settings = context.scene.rimvision
        record = record if record is not None else selected(context)
        if objects is None:
            roots = {model_root(obj) if obj.get("rimvision_def") else obj for obj in context.selected_objects if obj.type == "MESH" and not obj.get("rimvision_role")}
            if not roots and context.object and context.object.get("rimvision_role") == "anchor" and context.object.parent and context.object.parent.type == "MESH":
                roots.add(model_root(context.object.parent))
            objects = sorted({part for obj in roots for part in (obj, *obj.children_recursive) if part.type == "MESH" and not part.get("rimvision_role")}, key=lambda obj: obj.name)
        if context.mode != "OBJECT" or not objects or record is None:
            self.report({"ERROR"}, "Select a catalog entry and meshes in Object Mode")
            return {"CANCELLED"}
        if (record.get("category") not in ("Building", "Item", "Plant") and not
                (record.get("category") == "Pawn" and record.get("animal"))) or record.get("door", False):
            self.report({"ERROR"}, "Поддерживаются постройки, предметы, растения и животные; двери и другие пешки используют отдельный рендер")
            return {"CANCELLED"}
        try:
            if not settings.addon_path and not settings.output:
                raise ValueError("Select an output mod folder")
            if any(obj.get("rimvision_def") and obj["rimvision_def"] != record["defName"] for obj in objects):
                raise ValueError("Выделенные меши относятся к другому предмету. Выберите его в каталоге или сохраните коллекцию аддона.")
            if not re.fullmatch(r"[A-Za-z0-9_]+", record["defName"]):
                raise ValueError("ThingDef name is not safe for a filename")
            suffix = ""
            if settings.graphic_filter:
                import hashlib
                suffix = "_" + hashlib.sha256(settings.graphic_filter.encode("utf-8")).hexdigest()[:12]
            output_root = Path(bpy.path.abspath(settings.addon_path or settings.output))
            destination = output_root / "OptionalContent" / "RimVision" / "Models" / (record["defName"] + suffix + ".xml")
            owned_source = False
            sources = {obj.get("rimvision_source", "") for obj in objects}
            if settings.addon_path and len(sources) == 1 and "" not in sources:
                source = Path(next(iter(sources))).resolve()
                if source.is_file() and any(source.is_relative_to((output_root / "OptionalContent" / n / "Models").resolve()) for n in ("RimVision", "RimWorld3DVR")):
                    document = ET.parse(source).getroot()
                    if any(node.findtext("thingDef", "").strip() == record["defName"] and node.findtext("graphicPathContains", "").strip() == settings.graphic_filter for node in document):
                        destination = source
                        owned_source = True
            if destination.exists() and not settings.overwrite and not owned_source:
                raise ValueError("File already exists; enable Replace existing model file to overwrite it")
            root = ET.Element("Defs")
            model = ET.SubElement(root, "RimVisionModel")
            field(model, "thingDef", record["defName"])
            field(model, "heightOffset", number(settings.height_offset))
            if settings.graphic_filter:
                field(model, "graphicPathContains", settings.graphic_filter)
            vertices = ET.SubElement(model, "vertices")
            faces = ET.SubElement(model, "faces")
            vertex_count = 0
            graph = context.evaluated_depsgraph_get()
            sizes = {}
            textures = {}
            object_surfaces = {}
            for obj in objects:
                evaluated = obj.evaluated_get(graph)
                mesh = evaluated.to_mesh(preserve_all_data_layers=True, depsgraph=graph)
                if mesh is None:
                    raise ValueError(obj.name + ": cannot obtain mesh")
                try:
                    mesh.calc_loop_triangles()
                    points = [evaluated.matrix_world @ vertex.co for vertex in mesh.vertices]
                    for point in points:
                        vertex = ET.SubElement(vertices, "li")
                        field(vertex, "x", number(point.x + record["width"] * 0.5))
                        field(vertex, "height", number(point.z))
                        field(vertex, "z", number(point.y + record["depth"] * 0.5))
                    reverse_winding = evaluated.matrix_world.to_3x3().determinant() > 0
                    normal_matrix = evaluated.matrix_world.to_3x3().inverted().transposed()
                    for triangle in mesh.loop_triangles:
                        loops = list(triangle.loops)
                        if reverse_winding:
                            loops.reverse()
                        positions = [points[mesh.loops[i].vertex_index] for i in loops]
                        if (positions[1] - positions[0]).cross(positions[2] - positions[0]).length_squared <= 1e-16:
                            raise ValueError(obj.name + ": грань №" + str(triangle.polygon_index + 1) + " после модификаторов имеет нулевую или почти нулевую площадь. Проверьте совпадающие вершины и масштаб модели.")
                        material = mesh.materials[triangle.material_index] if triangle.material_index < len(mesh.materials) else None
                        surface = material.rimvision if material else None
                        from_object = surface is not None and surface.mode == "Object"
                        image, color, uv_name = None, None, ""
                        if from_object:
                            if material.as_pointer() not in object_surfaces:
                                object_surfaces[material.as_pointer()] = object_surface(material)
                            image, color, uv_name = object_surfaces[material.as_pointer()]
                        face = ET.SubElement(faces, "li")
                        field(face, "indices", ",".join(str(vertex_count + mesh.loops[i].vertex_index) for i in loops))
                        normals = [(normal_matrix @ mesh.corner_normals[i].vector).normalized() for i in loops]
                        if any(normal.length_squared < 0.5 for normal in normals):
                            raise ValueError(obj.name + ": invalid corner normal")
                        field(face, "normals", ";".join(number(normal.x) + "," + number(normal.z) + "," + number(normal.y) for normal in normals))
                        field(face, "smooth", str(mesh.polygons[triangle.polygon_index].use_smooth).lower())
                        field(face, "twoSided", str(not material.use_backface_culling if from_object else surface.two_sided if surface else True).lower())
                        if surface and (surface.mode == "Solid" or (from_object and image is None)):
                            field(face, "solidColor", ",".join(number(c) for c in (color if from_object else surface.color)))
                            field(face, "tintWithThing", str(surface.tint).lower())
                        else:
                            direction = surface.direction if surface else "Thing"
                            custom = surface is not None and (surface.mode in ("Custom", "Atlas") or from_object)
                            use_uv = from_object or surface is None or surface.mode == "Atlas" or surface.use_uv
                            uv_layer = mesh.uv_layers.get(uv_name) if uv_name else mesh.uv_layers.active
                            if custom:
                                if from_object:
                                    source = ("Object", image.as_pointer())
                                elif surface.mode == "Atlas":
                                    source = ("Atlas", record["defName"])
                                else:
                                    source = bpy.path.abspath(surface.texture_path)
                                if source not in textures:
                                    textures[source] = prepare_texture(surface, record, image)
                                texture_path, data, size = textures[source]
                                field(face, "texturePath", texture_path)
                                field(face, "tintWithThing", str(surface.tint).lower())
                                if use_uv and uv_layer is None:
                                    raise ValueError(obj.name + ": не найдена UV-развёртка " + (uv_name or "для текстуры"))
                            else:
                                field(face, "texture", direction)
                            pending = mesh.attributes.get("rimvision_pending_uv")
                            raw_u = mesh.attributes.get("rimvision_pixel_u")
                            raw_v = mesh.attributes.get("rimvision_pixel_v")
                            preserve_pixels = not custom and pending is not None and raw_u is not None and raw_v is not None and pending.data[triangle.polygon_index].value
                            if preserve_pixels and use_uv:
                                field(face, "uvPoints", ";".join(number(raw_u.data[i].value) + "," + number(raw_v.data[i].value) for i in loops))
                            elif uv_layer and use_uv:
                                if custom:
                                    width, height = size
                                elif direction not in sizes:
                                    path = sprite_path(record, direction)
                                    if not path or not Path(path).is_file():
                                        raise ValueError("Для экспорта UV подготовьте спрайты игры или отключите UV у материала.")
                                    image = image_for(record, direction)
                                    sizes[direction] = tuple(image.size)
                                if not custom:
                                    width, height = sizes[direction]
                                if width <= 0 or height <= 0:
                                    raise ValueError("Invalid sprite size")
                                coords = [uv_layer.data[i].uv for i in loops]
                                field(face, "uvPoints", ";".join(number(uv.x * width) + "," + number((1 - uv.y) * height) for uv in coords))
                                if not custom:
                                    field(face, "uvTextureSize", number(width) + "," + number(height))
                        if surface:
                            if surface.turret_top:
                                field(face, "turretTop", "true")
                            for prop, tag in (("required_links", "requiredLinks"), ("forbidden_links", "forbiddenLinks")):
                                value = getattr(surface, prop)
                                if value:
                                    if any(p.strip() not in ("North", "East", "South", "West") for p in value.split(",")):
                                        raise ValueError("Links must be North,East,South,West")
                                    field(face, tag, value)
                    vertex_count += len(mesh.vertices)
                finally:
                    evaluated.to_mesh_clear()
            helpers = {child for obj in objects for child in obj.children_recursive if child.get("rimvision_role")}
            cutouts = [obj for obj in helpers if obj.get("rimvision_role") == "ground_cutout"]
            if len(cutouts) > 1:
                raise ValueError("Можно экспортировать только один ground cutout на модель")
            for cutout in cutouts:
                if cutout.type != "MESH" or len(cutout.data.polygons) != 1:
                    raise ValueError("Ground cutout должен содержать одну грань")
                polygon = cutout.data.polygons[0]
                indices = list(polygon.vertices)
                if cutout.matrix_world.to_3x3().determinant() > 0:
                    indices.reverse()
                field(model, "groundCutout", ",".join(str(vertex_count + i) for i in range(len(indices))))
                for i in indices:
                    point = cutout.matrix_world @ cutout.data.vertices[i].co
                    vertex = ET.SubElement(vertices, "li")
                    field(vertex, "x", number(point.x + record["width"] * 0.5))
                    field(vertex, "height", number(point.z))
                    field(vertex, "z", number(point.y + record["depth"] * 0.5))
                vertex_count += len(indices)
            anchors = sorted((obj for obj in helpers if obj.get("rimvision_role") == "anchor"), key=lambda obj: obj.name)
            if anchors:
                anchor_node = ET.SubElement(model, "anchors")
                effect_kinds = set()
                for obj in anchors:
                    node = ET.fromstring(obj.get("rimvision_anchor_xml", "<li/>"))
                    effect = obj.rimvision_effect
                    if effect.kind in ("fire", "light"):
                        if effect.kind in effect_kinds:
                            raise ValueError("В модели допускается одна точка огня и одна точка света")
                        effect_kinds.add(effect.kind)
                        for key, value in (("name", effect.kind), ("size", number(effect.size)), ("radius", number(effect.radius)),
                                           ("intensity", number(effect.intensity)), ("color", ",".join(number(c) for c in effect.color)),
                                           ("always", str(effect.always).lower())):
                            existing = node.find(key)
                            if existing is None:
                                existing = ET.SubElement(node, key)
                            existing.text = value
                    point = obj.matrix_world.translation
                    for key, coordinate in (("x", point.x + record["width"] * 0.5), ("height", point.z), ("z", point.y + record["depth"] * 0.5)):
                        existing = node.find(key)
                        if existing is None:
                            existing = ET.SubElement(node, key)
                        existing.text = number(coordinate)
                    anchor_node.append(node)
            if not len(faces):
                raise ValueError("No faces to export")
            ET.indent(root, space="  ")
            destination.parent.mkdir(parents=True, exist_ok=True)
            if settings.addon_path and destination.is_file():
                document = ET.parse(destination).getroot()
                matches = [i for i, node in enumerate(document) if node.findtext("thingDef", "").strip() == record["defName"] and node.findtext("graphicPathContains", "").strip() == settings.graphic_filter]
                if matches:
                    index = matches[-1]
                    document.remove(document[index])
                    document.insert(index, model)
                else:
                    document.append(model)
                root = document
                ET.indent(root, space="  ")
            for texture_path, data, size in textures.values():
                target = output_root / "Textures" / (texture_path + ".png")
                target.parent.mkdir(parents=True, exist_ok=True)
                if not target.is_file():
                    target.write_bytes(data)
            if settings.addon_path:
                write_xml(root, destination)
            else:
                with destination.open("wb" if settings.overwrite else "xb") as output:
                    ET.ElementTree(root).write(output, encoding="utf-8", xml_declaration=True)
            for obj in objects:
                obj["rimvision_def"] = record["defName"]
                obj["rimvision_filter"] = settings.graphic_filter
                obj["rimvision_height_offset"] = settings.height_offset
                obj["rimvision_source"] = str(destination)
                attach_to_addon(context, obj)
            if settings.addon_path:
                add_dependency(output_root, record.get("packageId", ""), record.get("mod", ""))
                ensure_content(output_root)
                refresh_addon(settings)
                models = record.setdefault("models", [])
                source = dict(file=str(destination.resolve()), index=list(root).index(model), filter=settings.graphic_filter,
                              mod=settings.addon_name, legacy=destination.resolve().is_relative_to((output_root / "OptionalContent/RimWorld3DVR/Models").resolve()))
                existing = next((i for i, entry in enumerate(models) if Path(entry["file"]).resolve() == destination.resolve() and entry["filter"] == settings.graphic_filter), None)
                if existing is None:
                    models.append(source)
                else:
                    models[existing] = source
                _model_items[record["defName"]] = [(str(i), (entry["filter"] or "Основная") + " • " + entry["mod"], entry["file"], i) for i, entry in enumerate(models)]
                if selected(context) is record:
                    settings.model_choice = str(existing if existing is not None else len(models) - 1)
            self.report({"INFO"}, "Exported " + str(len(faces)) + " triangles to " + str(destination))
        except (OSError, ValueError, RuntimeError, ET.ParseError) as error:
            self.report({"ERROR"}, str(error))
            return {"CANCELLED"}
        return {"FINISHED"}


class RVAddToAddon(bpy.types.Operator):
    bl_idname = "rimvision.add_to_addon"
    bl_label = "Добавить выделенное в коллекцию аддона"
    bl_options = {"REGISTER", "UNDO"}

    def execute(self, context):
        settings = context.scene.rimvision
        record = selected(context)
        objects = [o for o in context.selected_objects if o.type == "MESH" and not o.get("rimvision_role")]
        if not settings.addon_path or record is None or not objects or context.mode != "OBJECT":
            self.report({"ERROR"}, "Откройте аддон, выберите предмет каталога и меши в Object Mode")
            return {"CANCELLED"}
        for obj in objects:
            if not obj.get("rimvision_def"):
                obj["rimvision_def"] = record["defName"]
                obj["rimvision_filter"] = settings.graphic_filter
                obj["rimvision_height_offset"] = settings.height_offset
            attach_to_addon(context, obj)
        return {"FINISHED"}


class RVSaveAddon(bpy.types.Operator):
    bl_idname = "rimvision.save_addon"
    bl_label = "Сохранить всю коллекцию"

    def execute(self, context):
        if _pending_meshes:
            attach_new_meshes()
        settings = context.scene.rimvision
        collection = settings.addon_collection
        if context.mode != "OBJECT" or not settings.addon_path or collection is None:
            self.report({"ERROR"}, "Откройте аддон в Object Mode")
            return {"CANCELLED"}
        groups = {}
        for obj in collection.all_objects:
            if obj.type == "MESH" and obj.get("rimvision_def") and not obj.get("rimvision_role"):
                root = model_root(obj)
                key = (root["rimvision_def"], root.get("rimvision_filter", ""), root.get("rimvision_height_offset", 0.0))
                groups.setdefault(key, []).append(obj)
        if not groups:
            self.report({"ERROR"}, "В коллекции аддона нет моделей")
            return {"CANCELLED"}
        records = {record["defName"]: record for record in _records}
        if any(key[0] not in records for key in groups):
            self.report({"ERROR"}, "Загрузите каталог игры с определениями всех моделей коллекции")
            return {"CANCELLED"}
        targets = [(key[0], key[1]) for key in groups]
        if len(set(targets)) != len(targets):
            self.report({"ERROR"}, "У одной модели разные смещения высоты; сохраните её отдельно")
            return {"CANCELLED"}
        previous = (settings.graphic_filter, settings.height_offset)
        saved = 0
        try:
            for (definition, graphic_filter, height), objects in sorted(groups.items()):
                settings.graphic_filter = graphic_filter
                settings.height_offset = height
                if RVExport._export(self, context, records[definition], objects) != {"FINISHED"}:
                    self.report({"WARNING"}, "Сохранено моделей: " + str(saved) + ". Исправьте ошибку и повторите сохранение.")
                    return {"CANCELLED"}
                saved += 1
        finally:
            settings.graphic_filter, settings.height_offset = previous
        self.report({"INFO"}, "Сохранено моделей в аддон: " + str(saved))
        return {"FINISHED"}


def draw_catalog(layout, context, rows=7):
    settings = context.scene.rimvision
    layout.prop(settings, "search", text="Поиск", icon="VIEWZOOM")
    row = layout.row(align=True)
    row.prop(settings, "category", text="Тип")
    row.prop(settings, "mod_filter", text="")
    layout.prop(settings, "models_only")
    layout.prop(settings, "missing_models_only")
    layout.template_list("RV_UL_catalog", "", settings, "entries", settings, "index", rows=rows)


def draw_item_card(layout, context):
    settings = context.scene.rimvision
    record = selected(context)
    if record is None:
        layout.label(text="Выберите предмет каталога")
        return
    box = layout.box()
    icon = preview_icon(record)
    if icon:
        row = box.row()
        row.alignment = "CENTER"
        row.template_icon(icon_value=icon, scale=7)
    box.label(text=record.get("label", record["defName"]), icon="OBJECT_DATA")
    box.label(text=record["defName"])
    box.label(text=record.get("mod", ""))
    if record.get("inactiveContent"):
        box.label(text="Мод / DLC выключен в игре", icon="INFO")
    if record.get("previewNote"):
        box.label(text=record["previewNote"], icon="INFO")
    box.label(text=str(record["width"]) + " × " + str(record["depth"]) + " клеток")
    builtin = record.get("builtin3d") or ("Дверь" if record.get("door") else "Стена" if record["defName"] == "Wall" else "")
    if builtin:
        locked = record.get("builtin3dLocked") or record.get("door")
        box.label(text="Встроенная 3D: " + builtin, icon="LOCKED" if locked else "MESH_CUBE")
        if locked:
            box.label(text="Замена модели пока не поддерживается")
            box.label(text="Геометрию создаёт отдельный рендер RimVision")
            box.label(text="Экспорт XML не заменит её в игре", icon="INFO")
        else:
            box.label(text="Встроенную геометрию можно заменить XML")
            box.label(text="Исходная геометрия из кода не импортируется")
    if not icon:
        box.label(text="Спрайт не найден", icon="IMAGE_DATA")
        if record.get("texturePath"):
            box.label(text="Обновите подготовку спрайтов", icon="INFO")
        else:
            box.label(text="В XML нет пути к отдельному спрайту", icon="INFO")
    if record.get("models"):
        box.label(text="Найдена XML-модель — посмотрите её", icon="CHECKMARK")
        box.label(text="Готовых моделей: " + str(len(record["models"])), icon="CHECKMARK")
        box.prop(settings, "model_choice", text="Вариант")
        box.operator("rimvision.create_template", text="Добавить готовую модель", icon="IMPORT")
    else:
        box.label(text="XML-модель не найдена")
        box.operator("rimvision.create_template", text="Создать шаблон модели", icon="ADD")
    row = box.row(align=True)
    if record.get("models"):
        row.operator("rimvision.create_template", text="Новая модель", icon="ADD").force_new = True
    row.operator("rimvision.import_model_file", text="XML…", icon="FILE_FOLDER")


class RVBrowser(bpy.types.Operator):
    bl_idname = "rimvision.browse_catalog"
    bl_label = "Каталог моделей RimVision"

    def invoke(self, context, event):
        return context.window_manager.invoke_props_dialog(self, width=850)

    def draw(self, context):
        split = self.layout.split(factor=0.65)
        draw_catalog(split.column(), context, 15)
        draw_item_card(split.column(), context)

    def execute(self, context):
        return {"FINISHED"}


def startup_objects(scene):
    settings = scene.rimvision
    result = []
    for collection in scene.collection.children:
        if collection.name != "Collection" or collection.users != 1 or collection in (settings.addon_collection, settings.guides):
            continue
        for obj in collection.objects:
            expected = {"Cube": "MESH", "Camera": "CAMERA", "Light": "LIGHT"}.get(obj.name)
            if obj.type != expected or obj.get("rimvision_def") or obj.get("rimvision_role"):
                continue
            if len(obj.users_collection) != 1 or len(obj.users_scene) != 1 or obj.parent or obj.children or obj.animation_data:
                continue
            if obj.type == "MESH" and (obj.modifiers or len(obj.data.vertices) != 8 or len(obj.data.polygons) != 6 or
                any(abs(abs(c) - 1) > 1e-6 for vertex in obj.data.vertices for c in vertex.co)):
                continue
            result.append(obj)
    return result


class RVAddEffect(bpy.types.Operator):
    bl_idname = "rimvision.add_effect"
    bl_label = "Добавить точку эффекта"
    bl_options = {"REGISTER", "UNDO"}
    kind: EnumProperty(items=[("fire", "Огонь", ""), ("light", "Свет", "")], default="fire")

    def execute(self, context):
        record = selected(context)
        root = context.scene.rimvision.current_model
        if context.mode != "OBJECT" or record is None or root is None or root.get("rimvision_def") != record["defName"]:
            self.report({"ERROR"}, "Сначала создайте или загрузите модель в Object Mode")
            return {"CANCELLED"}
        try:
            marker = next((obj for obj in root.children_recursive if obj.get("rimvision_role") == "anchor" and obj.rimvision_effect.kind == self.kind), None)
            if marker is None:
                marker = create_effect_marker(context, record, root, self.kind)
                attach_to_addon(context, marker)
            for obj in context.selected_objects:
                obj.select_set(False)
            marker.select_set(True)
            context.view_layer.objects.active = marker
            context.scene.rimvision.effect_options = True
            if self.kind == "light" and context.area and context.area.type == "VIEW_3D":
                context.space_data.shading.type = "MATERIAL"
                context.space_data.shading.use_scene_lights = True
        except (OSError, ValueError, RuntimeError) as error:
            self.report({"ERROR"}, str(error))
            return {"CANCELLED"}
        return {"FINISHED"}


class RVSelectEffect(bpy.types.Operator):
    bl_idname = "rimvision.select_effect"
    bl_label = "Выбрать точку эффекта"
    object_name: StringProperty()

    @classmethod
    def poll(cls, context):
        return context.mode == "OBJECT"

    def execute(self, context):
        obj = context.scene.objects.get(self.object_name)
        if obj is None or context.view_layer.objects.get(obj.name) is None:
            return {"CANCELLED"}
        for selected_obj in context.selected_objects:
            selected_obj.select_set(False)
        obj.select_set(True)
        context.view_layer.objects.active = obj
        return {"FINISHED"}


class RVStartWork(bpy.types.Operator):
    bl_idname = "rimvision.start_work"
    bl_label = "Начать работу"
    bl_options = {"REGISTER", "UNDO"}

    @classmethod
    def poll(cls, context):
        return context.mode == "OBJECT"

    def execute(self, context):
        for obj in startup_objects(context.scene):
            obj.select_set(False, view_layer=context.view_layer)
            if context.view_layer.objects.active == obj:
                context.view_layer.objects.active = None
            obj.hide_set(True, view_layer=context.view_layer)
            obj.hide_render = True
        context.view_layer.active_layer_collection = context.view_layer.layer_collection
        context.scene.rimvision.workflow_stage = "Setup"
        context.scene.rimvision.setup_options = True
        return {"FINISHED"}


class RVBackToSetup(bpy.types.Operator):
    bl_idname = "rimvision.back_to_setup"
    bl_label = "Назад к подготовке игры"

    def execute(self, context):
        context.scene.rimvision.workflow_stage = "Setup"
        return {"FINISHED"}


class RVClearStartup(bpy.types.Operator):
    bl_idname = "rimvision.clear_startup"
    bl_label = "Удалить куб, свет и камеру"
    bl_description = "Удалить стартовые объекты и опустевшую базовую коллекцию; действие можно отменить через Ctrl+Z"
    bl_options = {"REGISTER", "UNDO"}

    @classmethod
    def poll(cls, context):
        return context.mode == "OBJECT"

    def execute(self, context):
        settings = context.scene.rimvision
        removed = 0
        for collection in list(context.scene.collection.children):
            if collection.name != "Collection" or collection.users != 1 or collection in (settings.addon_collection, settings.guides):
                continue
            for obj in startup_objects(context.scene):
                if collection.objects.get(obj.name) is None:
                    continue
                data, kind = obj.data, obj.type
                bpy.data.objects.remove(obj, do_unlink=True)
                if data.users == 0:
                    getattr(bpy.data, {"MESH": "meshes", "CAMERA": "cameras", "LIGHT": "lights"}[kind]).remove(data)
                removed += 1
            if not collection.objects and not collection.children:
                bpy.data.collections.remove(collection)
        context.view_layer.update()
        reset_mesh_tracking()
        self.report({"INFO"}, "Удалено стартовых объектов: " + str(removed))
        return {"FINISHED"}


class RVPreviewMaterial(bpy.types.Operator):
    bl_idname = "rimvision.preview_material"
    bl_label = "Обновить материал в сцене"
    bl_options = {"REGISTER", "UNDO"}

    def execute(self, context):
        record = selected(context)
        obj = context.object
        if record is None or obj is None or obj.type != "MESH" or obj.active_material is None:
            return {"CANCELLED"}
        try:
            material_preview(obj.active_material, record)
        except (OSError, RuntimeError, ValueError) as error:
            self.report({"ERROR"}, str(error))
            return {"CANCELLED"}
        return {"FINISHED"}


class RVCleanResources(bpy.types.Operator):
    bl_idname = "rimvision.clean_resources"
    bl_label = "Навести порядок в ресурсах RimVision"
    bl_options = {"REGISTER", "UNDO"}

    def execute(self, context):
        paths, old_materials = {}, {}
        definitions = {record["defName"]: record for record in _records}
        for record in _records:
            for direction in ("North", "East", "South", "West"):
                for prefix in ("sprite", "baseSprite"):
                    path = record.get(prefix + direction)
                    if path:
                        paths.setdefault(str(Path(path).resolve()).casefold(), (record, direction))
            for suffix in ("surface", "game texture", "solid", "Thing", "North", "East", "South", "West"):
                old_materials.setdefault(record["defName"] + " " + suffix, record)
        for material in bpy.data.materials:
            record = old_materials.get(re.sub(r"\.\d+$", "", material.name))
            if record is not None and material.library is None and material.rimvision.mode != "Object":
                name_resource(material, record, "Материал")
            definition = material.get("rimvision_resource_def")
            record = definitions.get(definition)
            if record is not None:
                name_material(material, record)
            if definition and material.use_nodes:
                if record:
                    for node in material.node_tree.nodes:
                        if (node.type == "TEX_IMAGE" and node.image and node.image.get("rimvision_atlas") and
                            (node.image.get("rimvision_auto_name") or node.image.name.startswith("RimVision atlas "))):
                            name_resource(node.image, record, "Атлас 2×2")
        for image in bpy.data.images:
            if image.library is not None or not image.filepath:
                continue
            entry = paths.get(str(Path(bpy.path.abspath(image.filepath)).resolve()).casefold())
            if entry and re.fullmatch(r"[a-f0-9]{64}\.png(?:\.\d+)?", image.name):
                record, direction = entry
                actual = next((key for key, value in record.get("directionalSprites", {}).items()
                               if str(Path(value).resolve()).casefold() == str(Path(bpy.path.abspath(image.filepath)).resolve()).casefold()), "")
                kind = {"North": "Север", "South": "Юг", "East": "Восток", "West": "Запад"}.get(actual, "Спрайт")
                name_resource(image, record, kind)
        removed_materials, removed_images = 0, 0
        for material in list(bpy.data.materials):
            if material.get("rimvision_auto_name") == material.name and material.users == 0 and not material.use_fake_user and material.library is None:
                bpy.data.materials.remove(material)
                removed_materials += 1
        for image in list(bpy.data.images):
            managed = image.get("rimvision_auto_name") == image.name or (image.get("rimvision_atlas") and image.name.startswith("RimVision atlas "))
            if managed and image.users == 0 and not image.use_fake_user and not image.is_dirty and image.library is None:
                bpy.data.images.remove(image)
                removed_images += 1
        self.report({"INFO"}, "Удалено неиспользуемых материалов: " + str(removed_materials) + "; картинок: " + str(removed_images))
        return {"FINISHED"}


def foldout(layout, settings, prop, title):
    box = layout.box()
    expanded = getattr(settings, prop)
    box.prop(settings, prop, text=title, icon="TRIA_DOWN" if expanded else "TRIA_RIGHT", emboss=False, toggle=True)
    return box.column() if expanded else None


def draw_setup(layout, context):
    settings = context.scene.rimvision
    setup = layout
    game_found = bool(settings.game and (Path(bpy.path.abspath(settings.game)) / "Data/Core").is_dir())
    setup.enabled = _extracting is None
    workshop_found = bool(settings.workshop and Path(bpy.path.abspath(settings.workshop)).is_dir())
    config_found = bool(settings.config and Path(bpy.path.abspath(settings.config)).is_file())
    setup.label(text="Игра найдена" if game_found else "Игра не найдена — укажите путь", icon="CHECKMARK" if game_found else "ERROR")
    setup.label(text="Workshop найден" if workshop_found else "Workshop не найден", icon="CHECKMARK" if workshop_found else "INFO")
    setup.label(text="Список активных модов найден" if config_found else "Список активных модов не найден", icon="CHECKMARK" if config_found else "INFO")
    setup.label(text="Каталог загружен: " + str(len(_records)) + " предметов" if _records else "Каталог ещё не загружен", icon="CHECKMARK" if _records else "INFO")
    sprites_ready = settings.sprites_ready and settings.sprite_status_context == sprite_status_context(settings)
    if _extracting and _extracting._scene == context.scene:
        setup.label(text="Спрайты подготавливаются…", icon="TIME")
    else:
        setup.label(text="Спрайты подготовлены: " + str(settings.sprite_count) if sprites_ready else "Спрайты не подготовлены для текущих модов", icon="CHECKMARK" if sprites_ready else "INFO")
    setup.operator("rimvision.find_game", icon="VIEWZOOM")
    setup.operator("rimvision.prepare_sprites", icon="IMAGE_DATA")
    setup.prop(settings, "advanced", icon="PREFERENCES")
    if settings.advanced:
        for prop in ("game", "workshop", "model_root", "config", "version", "active_only"):
            setup.prop(settings, prop)
        setup.operator("rimvision.load_catalog", text="Перечитать папки", icon="FILE_REFRESH").source = "Files"


def draw_addon_tools(layout, context):
    settings = context.scene.rimvision
    addon = layout
    row = addon.row(align=True)
    row.operator("rimvision.create_addon", icon="ADD")
    row.operator("rimvision.open_addon", icon="FILE_FOLDER")
    addon.operator("rimvision.find_addons", icon="FILE_REFRESH")
    addon.label(text=settings.addon_discovery_status)
    if settings.found_addons:
        addon.template_list("RV_UL_found_addons", "", settings, "found_addons", settings, "found_addon_index", rows=3)
        if 0 <= settings.found_addon_index < len(settings.found_addons):
            found = settings.found_addons[settings.found_addon_index]
            addon.label(text=found.origin + ": " + found.path, icon="FILE_FOLDER")
        addon.operator("rimvision.open_found_addon", icon="IMPORT")
    if settings.addon_path:
        addon.label(text=settings.addon_name)
        addon.prop(settings, "addon_metadata_options", icon="PREFERENCES")
        if settings.addon_metadata_options:
            addon.prop(settings, "addon_edit_name")
            addon.operator("rimvision.edit_addon_description", icon="TEXT")
            addon.prop(settings, "addon_preview")
            preview = bpy.path.abspath(settings.addon_preview) if settings.addon_preview else ""
            if preview and Path(preview).is_file():
                try:
                    if preview not in _previews:
                        _previews.load(preview, preview, "IMAGE")
                    addon.template_icon(icon_value=_previews[preview].icon_id, scale=6)
                except (OSError, RuntimeError, KeyError):
                    addon.label(text="Не удалось показать превью", icon="ERROR")
            addon.operator("rimvision.save_addon_metadata", icon="FILE_TICK")
        addon.label(text=bpy.path.abspath(settings.addon_path), icon="FILE_FOLDER")
        addon.template_list("RV_UL_addon", "", settings, "addon_models", settings, "addon_index", rows=4)
        row = addon.row(align=True)
        row.operator("rimvision.load_addon_model", text="Загрузить модель", icon="IMPORT")
        row.operator("rimvision.refresh_addon", text="", icon="FILE_REFRESH")
        addon.operator("rimvision.add_to_addon", text="Добавить выделенное в коллекцию", icon="ADD")
        addon.operator("rimvision.save_addon", icon="EXPORT")


class RVPanel(bpy.types.Panel):
    bl_label = "RimVision Models"
    bl_idname = "RIMVISION_PT_models"
    bl_space_type = "VIEW_3D"
    bl_region_type = "UI"
    bl_category = "RimVision"

    def draw(self, context):
        layout = self.layout
        settings = context.scene.rimvision
        if settings.workflow_stage == "Auto" and not settings.addon_path and not settings.current_model and not any(obj.get("rimvision_def") for obj in context.scene.objects) and startup_objects(context.scene):
            layout.label(text="Куб, камера и свет будут скрыты", icon="INFO")
            row = layout.row()
            row.scale_y = 1.6
            row.operator("rimvision.start_work", icon="PLAY")
            if context.mode != "OBJECT":
                layout.label(text="Перейдите в Object Mode", icon="INFO")
            return
        if settings.workflow_stage == "Setup":
            layout.label(text="1. Игра и спрайты", icon="VIEWZOOM")
            draw_setup(layout.column(), context)
            layout.label(text=settings.status)
            if _extracting:
                layout.label(text="Esc — отменить извлечение")
            return
        if settings.workflow_stage == "Addons":
            layout.label(text="2. Выберите или создайте аддон", icon="OUTLINER_COLLECTION")
            draw_addon_tools(layout, context)
            layout.operator("rimvision.back_to_setup", icon="BACK")
            return
        game_found = bool(settings.game and (Path(bpy.path.abspath(settings.game)) / "Data/Core").is_dir())
        layout.label(text="Игра найдена" if game_found else "Игра не найдена", icon="CHECKMARK" if game_found else "ERROR")
        record = selected(context)
        if record:
            layout.label(text=record.get("label", record["defName"]), icon="OBJECT_DATA")
        layout.label(text=settings.status)
        if _extracting:
            layout.label(text="Esc — отменить извлечение")
        addon = foldout(layout, settings, "addon_options", "Аддон: " + settings.addon_name if settings.addon_path else "Аддон моделей")
        if addon is not None:
            draw_addon_tools(addon, context)
        setup = foldout(layout, settings, "setup_options", "Игра и пути")
        if setup is not None:
            draw_setup(setup, context)
        catalog = foldout(layout, settings, "catalog_options", "Каталог (" + str(len(_records)) + ")")
        if catalog is not None:
            catalog.operator("rimvision.browse_catalog", text="Открыть большой каталог", icon="VIEWZOOM")
            draw_catalog(catalog, context, rows=4)
        model = foldout(layout, settings, "model_options", "Текущая модель")
        if model is not None:
            model.operator("rimvision.clear_startup", icon="TRASH")
            draw_item_card(model, context)
            model.prop(settings, "auto_attach_meshes")
            if settings.current_model:
                model.label(text="Текущая модель: " + settings.current_model.name, icon="MESH_DATA")
            else:
                model.label(text="Создайте или загрузите модель для Shift+A", icon="INFO")
        reference = foldout(layout, settings, "reference_options", "Референс в сцене")
        if reference is not None:
            reference.prop(settings, "auto_reference")
            reference.prop(settings, "reference_all_sides")
            manual = reference.column()
            manual.enabled = not settings.reference_all_sides
            manual.prop(settings, "reference_direction", text="Вид")
            manual.prop(settings, "reference_side", text="Сторона")
            manual.prop(settings, "reference_rotation", text="Поворот XYZ")
            reference.prop(settings, "reference_gap")
            reference.prop(settings, "reference_offset", text="Смещение")
            reference.prop(settings, "reference_opacity", slider=True)
            reference.operator("rimvision.show_reference")
        effects = foldout(layout, settings, "effect_options", "Огонь и свет")
        if effects is not None:
            row = effects.row(align=True)
            row.enabled = settings.current_model is not None
            row.operator("rimvision.add_effect", text="🔥 Огонь", icon="MOD_FLUIDSIM").kind = "fire"
            row.operator("rimvision.add_effect", text="💡 Свет", icon="LIGHT_DATA").kind = "light"
            if settings.current_model is None:
                effects.label(text="Сначала создайте или загрузите модель", icon="INFO")
            if settings.current_model:
                for marker in settings.current_model.children_recursive:
                    if marker.get("rimvision_role") == "anchor" and marker.rimvision_effect.kind in ("fire", "light"):
                        effects.operator("rimvision.select_effect", text=marker.name, icon="LIGHT_DATA" if marker.rimvision_effect.kind == "light" else "MOD_FLUIDSIM").object_name = marker.name
            marker = context.object
            if marker and marker.get("rimvision_role") == "anchor" and marker.rimvision_effect.kind in ("fire", "light"):
                effect = marker.rimvision_effect
                effects.prop(marker, "location", text="Положение")
                if effect.kind == "fire":
                    effects.prop(effect, "size")
                    effects.prop(effect, "always")
                else:
                    effects.prop(effect, "color")
                    effects.prop(effect, "intensity")
                    effects.prop(effect, "radius")
                    effects.label(text="В игре нужен источник света у предмета", icon="INFO")
                effects.label(text="Перемещайте точку через G; удаляйте через X")
        material = context.object.active_material if context.object and context.object.type == "MESH" else None
        box = foldout(layout, settings, "surface_options", "Материал и текстуры")
        if box is not None:
            box.operator("rimvision.clean_resources", icon="BRUSH_DATA")
            if material is None:
                box.label(text="Выберите меш с материалом", icon="INFO")
            else:
                box.label(text=material.name)
                surface = material.rimvision
                box.prop(surface, "mode")
                if surface.mode == "Solid":
                    box.prop(surface, "color")
                    box.prop(surface, "tint")
                elif surface.mode == "Custom":
                    box.prop(surface, "texture_path")
                    box.prop(surface, "use_uv")
                    box.prop(surface, "tint")
                    box.label(text="Картинка сохранится в аддон как PNG")
                elif surface.mode == "Object":
                    box.label(text="Цвет и картинка из Base Color материала")
                    box.label(text="Используется UV-развёртка текстуры")
                    box.prop(surface, "tint")
                elif surface.mode == "Atlas":
                    box.label(text="Одна текстура 2×2 для всех ракурсов")
                    box.label(text="Сверху: North | East")
                    box.label(text="Снизу: South | West")
                    box.label(text="Разместите UV на нужных тайлах")
                    box.label(text="Атлас сохранится в аддон как PNG")
                    box.prop(surface, "tint")
                else:
                    box.prop(surface, "direction")
                    box.prop(surface, "use_uv")
                    box.operator("rimvision.use_sprite")
                for prop in ("two_sided", "turret_top", "required_links", "forbidden_links"):
                    if surface.mode == "Object" and prop == "two_sided":
                        continue
                    box.prop(surface, prop)
                if surface.mode != "Object":
                    box.operator("rimvision.preview_material")
        output = foldout(layout, settings, "export_options", "Сохранение и экспорт")
        if output is not None:
            if settings.addon_path:
                output.label(text="Аддон: " + settings.addon_name)
            else:
                output.prop(settings, "output", text="Папка мода")
            if settings.advanced or settings.graphic_filter or settings.height_offset:
                output.prop(settings, "graphic_filter", text="Фильтр графики")
                output.prop(settings, "height_offset", text="Смещение высоты")
            output.prop(settings, "overwrite", text="Заменить существующий XML")
            output.operator("rimvision.export_model", text="Сохранить модель в аддон" if settings.addon_path else "Экспортировать модель", icon="EXPORT")


_classes = (RVEntry, RVAddonModel, RVFoundAddon, RVEffectSettings, RVSettings, RVSurface, RV_UL_catalog, RV_UL_addon, RV_UL_found_addons, RVFindAddons, RVOpenFoundAddon, RVLoad, RVFind, RVPrepareSprites, RVReference,
            RVImport, RVImportFile, RVTemplate, RVTexture, RVCreateAddon, RVOpenAddon, RVRefreshAddon, RVLoadAddonModel,
            RVEditAddonDescription, RVSaveAddonMetadata, RVExport, RVAddToAddon, RVSaveAddon, RVBrowser, RVAddEffect, RVSelectEffect, RVStartWork, RVBackToSetup, RVClearStartup, RVPreviewMaterial, RVCleanResources, RVPanel)


def initial_paths():
    scenes = getattr(bpy.data, "scenes", None)
    if scenes is None:
        return 0.1
    reset_mesh_tracking()
    for scene in scenes:
        if scene.rimvision.addon_path and scene.rimvision.addon_description is None:
            try:
                load_addon_metadata(scene.rimvision)
            except (OSError, ValueError, ET.ParseError, RuntimeError) as error:
                scene.rimvision.status = str(error)
        if not scene.rimvision.game:
            try:
                locate(scene.rimvision)
            except (OSError, ValueError) as error:
                scene.rimvision.status = str(error)
        try:
            refresh_found_addons(scene.rimvision)
        except (OSError, ValueError, ET.ParseError, RuntimeError) as error:
            scene.rimvision.addon_discovery_status = str(error)
        try:
            refresh_sprite_status(scene.rimvision)
        except (OSError, ValueError, ET.ParseError, RuntimeError) as error:
            set_sprite_status(scene.rimvision, {}, {})
            print("[RimVision] Спрайты: " + str(error))


def register():
    global _previews
    for cls in _classes:
        bpy.utils.register_class(cls)
    bpy.types.Scene.rimvision = PointerProperty(type=RVSettings)
    bpy.types.Material.rimvision = PointerProperty(type=RVSurface)
    bpy.types.Object.rimvision_effect = PointerProperty(type=RVEffectSettings)
    _previews = bpy.utils.previews.new()
    _pending_meshes.clear()
    _known_meshes.clear()
    bpy.app.handlers.depsgraph_update_post.append(track_new_meshes)
    for handlers in (bpy.app.handlers.undo_post, bpy.app.handlers.redo_post, bpy.app.handlers.load_post):
        handlers.append(reset_mesh_tracking)
    bpy.app.timers.register(initial_paths, first_interval=0.0)


def unregister():
    global _previews
    if track_new_meshes in bpy.app.handlers.depsgraph_update_post:
        bpy.app.handlers.depsgraph_update_post.remove(track_new_meshes)
    for handlers in (bpy.app.handlers.undo_post, bpy.app.handlers.redo_post, bpy.app.handlers.load_post):
        if reset_mesh_tracking in handlers:
            handlers.remove(reset_mesh_tracking)
    if bpy.app.timers.is_registered(attach_new_meshes):
        bpy.app.timers.unregister(attach_new_meshes)
    _pending_meshes.clear()
    _known_meshes.clear()
    if bpy.app.timers.is_registered(initial_paths):
        bpy.app.timers.unregister(initial_paths)
    if _extracting:
        _extracting.cancel(bpy.context)
    del bpy.types.Material.rimvision
    del bpy.types.Object.rimvision_effect
    del bpy.types.Scene.rimvision
    for cls in reversed(_classes):
        bpy.utils.unregister_class(cls)
    bpy.utils.previews.remove(_previews)
    _previews = None
    _records.clear()
