import ctypes
import os
import threading
import time
from dataclasses import dataclass
from typing import List, Optional
import re

import configparser
import psutil

from memory_reader import GameState, MenuMods, GameplayData, OsuMemoryReader
from gui import ManiaGUI
from safe_print import safe_print
from osu_unlocker import OsuUnlocker

import keyboard

class HitObject(ctypes.Structure):
	_fields_ = [
		("x", ctypes.c_int),
		("y", ctypes.c_int),
		("timestamp", ctypes.c_int),
		("object_type", ctypes.c_int),
		("end_time", ctypes.c_int),
	]

@dataclass
class BeatmapSession:
	identifier: str
	map_id: int
	title: str
	difficulty: str
	path: str
	keys: int
	lane_positions: List[int]
	hit_objects: List[HitObject]
	first_hit_time: int
	first_hit_time_original: int
	mods_string: str
	speed_multiplier: float

# Global variable to track drift
drift_amount = 0.01
current_drift = 0

def auto_detect_osu_songs_dir() -> str:
	try:
		for process in psutil.process_iter(["pid", "name", "exe"]):
			name = process.info.get("name")
			if name and name.lower() == "osu!.exe":
				exe_path = process.info.get("exe")
				if exe_path:
					osu_dir = os.path.dirname(exe_path)
					songs_dir = os.path.join(osu_dir, "Songs")
					if os.path.isdir(songs_dir):
						return songs_dir
	except Exception:
		pass

	try:
		appdata = os.environ.get("LOCALAPPDATA", "")
		if appdata:
			fallback_dir = os.path.join(appdata, "osu!", "Songs")
			if os.path.isdir(fallback_dir):
				return fallback_dir
	except Exception:
		pass

	return ""

def parse_osu_file(file_path: str, speed_multiplier: float = 1.0) -> List[HitObject]:
	hit_objects: List[HitObject] = []
	try:
		with open(file_path, "r", encoding="utf-8") as osu_file:
			in_hit_object_section = False
			for raw_line in osu_file:
				line = raw_line.strip()
				if not in_hit_object_section:
					if line == "[HitObjects]":
						in_hit_object_section = True
					continue

				if not line:
					break

				parts = line.split(",")
				if len(parts) < 5:
					continue

				try:
					x = int(parts[0])
					y = int(parts[1])
					timestamp = int(int(parts[2]) / speed_multiplier)
					object_type = int(parts[3])
				except ValueError:
					continue

				is_hold = bool(object_type & 128)
				end_time = timestamp
				if is_hold and len(parts) >= 6:
					hold_data = parts[5].split(":")[0]
					try:
						end_time = int(int(hold_data) / speed_multiplier)
					except ValueError:
						end_time = timestamp

				hit_objects.append(HitObject(x, y, timestamp, object_type, end_time))
	except FileNotFoundError:
		pass
	except Exception:
		pass

	hit_objects.sort(key=lambda obj: obj.timestamp)
	return hit_objects

def get_lane_positions(hit_objects: List[HitObject]) -> List[int]:
	original_positions = sorted({obj.x for obj in hit_objects})
	return original_positions

def map_x_to_cs_position(x: int, cs_keys: int) -> int:
	position_width = 512 / cs_keys
	position = int(x / position_width)
	return min(position, cs_keys - 1)

def remap_hit_objects_to_cs_positions(hit_objects: List[HitObject], cs_keys: int) -> List[HitObject]:
	position_width = 512 / cs_keys
	remapped_objects = []

	for obj in hit_objects:
		position_index = map_x_to_cs_position(obj.x, cs_keys)
		new_x = int((position_index + 0.5) * position_width)
		remapped_objects.append(
			HitObject(
				x=new_x,
				y=obj.y,
				timestamp=obj.timestamp,
				object_type=obj.object_type,
				end_time=obj.end_time
			)
		)

	return remapped_objects

def get_first_hit_time_original(file_path: str) -> int:
	try:
		with open(file_path, "r", encoding="utf-8") as osu_file:
			in_hit_object_section = False
			for raw_line in osu_file:
				line = raw_line.strip()
				if not in_hit_object_section:
					if line == "[HitObjects]":
						in_hit_object_section = True
					continue
				if not line:
					break
				parts = line.split(",")
				if len(parts) >= 5:
					try:
						return int(parts[2])
					except ValueError:
						continue
	except Exception:
		pass
	return 0

class ManiaBotController:
	def __init__(self, use_gui: bool = True) -> None:
		self.base_dir = os.path.dirname(os.path.abspath(__file__))
		self.config_path = os.path.join(self.base_dir, "config.ini")
		self.config = configparser.ConfigParser()
		if os.path.exists(self.config_path):
			self.config.read(self.config_path, encoding="utf-8")

		self.dll = self._load_mania_dll()
		self.reader = OsuMemoryReader(debug=False)

		self.offset = self._get_config_int("bot", "offset", 30)
		self.timing_shift = self._get_config_int("bot", "timing_shift", 0)
		self.start_lead_ms = 0

		self.songs_dir = self._resolve_songs_dir()

		self.active_session: Optional[BeatmapSession] = None
		self.click_thread: Optional[threading.Thread] = None
		self.script_running = False
		self.shutdown = False
		self.last_state: Optional[GameState] = None
		self.last_log_time = 0.0
		self.last_timing_log = 0.0
		self.state_lock = threading.RLock()
		self.play_state_entry_time = 0.0

		self.resume_pending = False
		self.resume_target_index = 0
		self.resume_target_time = 0
		self.audio_timer_stabilized = False

		self.last_audio_time: Optional[int] = None
		self.audio_freeze_start_time: Optional[float] = None
		self.audio_freeze_value: Optional[int] = None
		self.is_paused = False
		self.pause_detection_enabled = False
		self.player_died = False

		self.use_gui = use_gui
		self.gui: Optional[ManiaGUI] = None
		self.bot_enabled = True
		self.osu_unlocker = OsuUnlocker()

		if self.use_gui:
			self.gui = ManiaGUI()
			self.gui.on_start_bot = self._gui_start_bot
			self.gui.on_stop_bot = self._gui_stop_bot
			self.gui.on_exit = self._gui_exit
			self.gui.on_offset_change = self._gui_offset_changed
			self.gui.on_timing_shift_change = self._gui_timing_shift_changed
			self.gui.on_osu_unlock_scan = self._gui_osu_unlock_scan
			self.gui.on_osu_unlock_unlock = self._gui_osu_unlock_unlock

		self.custom_keybinds = self._parse_custom_keybinds()
		self.shortcuts = self._parse_shortcuts()

		if self.timing_shift:
			self.dll.setTimingShift(ctypes.c_int(self.timing_shift))
		self.dll.setOffset(ctypes.c_int(self.offset))

		self.keyboard_listener_thread: Optional[threading.Thread] = None
		if keyboard is None:
			safe_print("Keyboard module not available. Shortcut keys disabled.")
		else:
			self.keyboard_listener_thread = threading.Thread(target=self._keyboard_listener, daemon=True)
			self.keyboard_list