import os
import yaml
import aiohttp
import subprocess
import shlex
import psutil
import asyncio
from PyQt5 import QtWidgets, QtGui, QtCore
from PyQt5.QtWidgets import QLabel
from PyQt5.QtCore import QTimer
from PyQt5.QtWidgets import QFileDialog, QGridLayout, QVBoxLayout, QHBoxLayout, QGroupBox, QApplication
from PyQt5.QtGui import QPixmap, QImage
from pyz3r import ALTTPR
from PIL import Image
import configparser
import json
import copy
import requests
import re
from io import BytesIO
from qasync import QEventLoop
import random
from PyQt5.QtGui import QFontDatabase
from datetime import datetime
import pytz
import shutil  # For copying MSU and PCM files to the correct folder
import glob  # For finding PCM files in the MSU folder
import math
import numpy as np
import sounddevice as sd
import wave
import io


import pygame
from pydub import AudioSegment
from qasync import QEventLoop, asyncSlot  # Import qasync for asyncio integration



def resource_path(relative_path):
    """Get the absolute path to the resource, works for both dev and PyInstaller."""
    try:
        # PyInstaller creates a temp folder and stores path in _MEIPASS
        base_path = sys._MEIPASS
    except Exception:
        base_path = os.path.abspath(".")

    return os.path.join(base_path, relative_path)

def audio_callback(indata, frames, time, status, app):
    """Callback function to process audio data and emit amplitude data."""
    try:
        # Compute amplitude data from the audio input
        amplitude_data = np.abs(indata).mean(axis=1)
        amplitude_data = np.clip(amplitude_data, 0, 1)  # Ensure values are between 0 and 1

        # Emit the amplitude data to the visualizer via the signal
        if app.audio_visualizer:
            app.audio_visualizer.amplitude_signal.emit(amplitude_data)


    except Exception as e:
        print(f"Error in audio callback: {e}")


class AudioVisualizer(QtWidgets.QWidget):
    # Define a custom signal that carries a NumPy array
    amplitude_signal = QtCore.pyqtSignal(object)

    def __init__(self, app, parent=None):
        super().__init__(parent)
                # Define the font family

        self.app = app  # Reference to the main application
        self.amplitude_data = np.zeros(32)  # Number of bars
        self.setMinimumSize(300, 100)  # Adjusted size for more bars
        self.setMaximumSize(300, 100)
        self.setSizePolicy(QtWidgets.QSizePolicy.Fixed, QtWidgets.QSizePolicy.Fixed)

        # Set up a timer for smoother animations
        self.animation_timer = QtCore.QTimer()
        self.animation_timer.timeout.connect(self.update)
        self.animation_timer.start(30)  # Update every 30 milliseconds (~33 FPS)

        # Initialize target and current amplitudes for smooth transitions
        self.target_amplitudes = np.zeros_like(self.amplitude_data)
        self.current_amplitudes = np.zeros_like(self.amplitude_data)

        # Sensitivity factor (default value)
        self.sensitivity = 2.0  # Initial sensitivity multiplier

        # Default gradient colors
        self.top_color = QtGui.QColor(255, 69, 0)    # OrangeRed
        self.bottom_color = QtGui.QColor(30, 144, 255)  # DodgerBlue

        # Connect the custom signal to the update_visualizer slot
        self.amplitude_signal.connect(self.update_visualizer)

    def set_gradient_colors(self, top_color, bottom_color):
        """Set the gradient colors for the visualizer bars."""
        self.top_color = top_color
        self.bottom_color = bottom_color
        self.update()  # Trigger a repaint to apply new colors

    def reset_amplitudes(self):
        """Gradually reset the visualizer's amplitudes to zero."""
        self.target_amplitudes = np.zeros_like(self.amplitude_data) + 10
        # Do NOT reset self.current_amplitudes here
        # The existing interpolation in paintEvent will handle the gradual transition
        self.update()  # Trigger a repaint to start the transition

    @QtCore.pyqtSlot(object)
    def update_visualizer(self, amplitude_data=None):
        """Update the visualizer with audio amplitude data."""
        if amplitude_data is None:
            amplitude_data = np.zeros_like(self.amplitude_data)


        # Ensure amplitude_data matches the number of bars
        amplitude_data = np.interp(
            np.linspace(0, len(amplitude_data), len(self.amplitude_data)),
            np.arange(len(amplitude_data)),
            amplitude_data
        )

        # Get the volume level from the main application
        volume_level = getattr(self.app, 'volume_level', 1.0)  # Default to 1.0 if not set

        # Fixed Scaling Factor
        scaling_factor = 375  # Adjust based on visualizer size and desired bar heights

        # Apply scaling and volume level, and include sensitivity
        amplitude_data *= scaling_factor * volume_level * self.sensitivity

        # Set the target amplitudes for animation
        self.target_amplitudes = amplitude_data

    def paintEvent(self, event):
        """Custom painting for the visualizer."""
        if not self.isVisible() or self.width() == 0 or self.height() == 0:
            return  # Prevent painting if widget is not visible or has no size

        painter = QtGui.QPainter(self)
        if not painter.isActive():
            print("[Visualizer] QPainter is not active.")
            return  # Prevent further execution if QPainter failed to initialize

        painter.setRenderHint(QtGui.QPainter.Antialiasing)

        # Calculate bar width and spacing
        bar_count = len(self.current_amplitudes)
        total_spacing = self.width() * 0.3  # 30% of the width for spacing
        bar_width = (self.width() - total_spacing) / bar_count
        spacing = total_spacing / (bar_count - 1) if bar_count > 1 else 0

        # Create a gradient brush for the bars using current gradient colors
        gradient = QtGui.QLinearGradient(0, 0, 0, self.height())
        gradient.setColorAt(0.0, self.top_color)    # Top color
        gradient.setColorAt(1.0, self.bottom_color)  # Bottom color
        brush = QtGui.QBrush(gradient)
        painter.setBrush(brush)
        painter.setPen(QtCore.Qt.NoPen)

        # Smoothly interpolate current amplitudes towards target amplitudes
        self.current_amplitudes += (self.target_amplitudes - self.current_amplitudes) * 0.2

        # Draw the bars
        for i, amplitude in enumerate(self.current_amplitudes):
            bar_height = amplitude  # amplitude already scaled to pixel height
            # Prevent bars from exceeding widget's height
            bar_height = min(bar_height, self.height())
            x = i * (bar_width + spacing)
            y = self.height() - bar_height
            rect = QtCore.QRectF(x, y, bar_width, bar_height)
            painter.drawRoundedRect(rect, 2, 2)  # Rounded corners for aesthetics


class ALTTPRSeedGeneratorApp(QtWidgets.QMainWindow):
    def __init__(self):
        super().__init__()
        self.is_playing = False  # Flag to track if a track is currently playing
        self.font_family = "The Legend of Zelda: A Link to "  # Ensure this font is installed or use a fallback
        self.is_paused = False
        self.payload = {}
        self.playlist = []  # Initialize playlist as an empty list
        self.init_mixer()
        self.loading_config = True  # Initialize this early
        self.header_color = ""
        # Initialize path_inputs and path_rows early
        self.path_inputs = {}
        self.path_rows = {}

        # Paths and configuration
        self.config = configparser.ConfigParser()
        self.config_file = "config.ini"

        # Add sprite loading attributes
        self.spritesheet = None
        self.sprite_data = None
        self.sprite_display_label_in_actions = QtWidgets.QLabel()

        # Load the sprite sheet and data
        self.load_sprites()

        self.customizer_url = "https://alttpr.com/api/customizer"
        self.randomizer_url = "https://alttpr.com/api/randomizer"
        self.randomizer_presets = ["crosskeys", "superquick", "default", "beginner", "entrances", "retrance", "keysanity"]
        self.customizer_presets = ["openboots", "enemizer"]

        self.patch_settings = {
            "heartspeed": "half",
            "heartcolor": "red",
            "spritename": "Old Man",
            "music": True,
            "quickswap": True,
            "menu_speed": "normal",
            "msu1_resume": True
        }

        self.update_timer = QtCore.QTimer(self)
        self.update_timer.timeout.connect(self.check_next_track)
        self.update_timer.start(500)  # Check every 500ms

        self.seed_update_timer = QtCore.QTimer(self)
        self.seed_update_timer.timeout.connect(self.on_update_seed_info_timeout)

        # Initialize the volume level before creating the AudioVisualizer
        self.volume_level = 0.3  # Increased volume level (30%)

        # Setup the UI
        self.init_ui()


        self.load_config()
        self.loading_config = False

        # After loading config, update the sprite display in the actions box
        self.update_sprite_display_in_actions()

        # Start the audio stream after the UI is set up
        self.start_audio_stream()


    def play_audio_directly(self, file_path):
        """Play audio and capture its data for the visualizer."""
        try:
            sound = pygame.mixer.Sound(file_path)
            sound.play()
            print(f"[PlayAudio] Playing audio: {file_path}")
        except Exception as e:
            self.show_message(f"Failed to play audio: {e}")
            print(f"[PlayAudio] Failed to play audio: {e}")
    
    def fetch_audio_data(self):
        """Fetch audio data from the mixer and update the visualizer."""
        try:
            # Access the mixer’s channel data
            channel = pygame.mixer.Channel(0)  # Assuming channel 0
            if channel.get_busy():
                # Get the current sound being played
                sound = channel.get_sound()
                if sound:
                    # Retrieve raw audio data
                    raw_data = sound.get_raw()
                    # Convert raw data to NumPy array
                    audio_data = np.frombuffer(raw_data, dtype=np.int16)
                    # Normalize audio data
                    audio_data = audio_data / 32768.0
                    # Compute amplitude
                    amplitude = np.abs(audio_data).mean()
                    
                    # Emit to visualizer
                    if self.audio_visualizer:
                        self.audio_visualizer.amplitude_signal.emit(np.array([amplitude]*16))
              
        except Exception as e:
            print(f"Error fetching audio data: {e}")



    def save_emulator_preference(self):
        """Save the selected emulator to the config file."""
        selected_emulator = "retroarch" if self.retroarch_radio.isChecked() else "snes9x"

        # Save the selected emulator to the config
        if "Emulator" not in self.config:
            self.config.add_section("Emulator")

        self.config["Emulator"]["selected_emulator"] = selected_emulator

        # Write to the config file
        with open(self.config_file, "w") as configfile:
            self.config.write(configfile)
                
    def start_audio_stream(self):
        """Start the audio stream for capturing audio data."""
        try:
            if hasattr(self, 'stream') and self.stream.active:
                self.stream.stop()  # Stop any existing streams before starting a new one
            self.stream = sd.InputStream(callback=lambda indata, frames, time, status: audio_callback(indata, frames, time, status, self))
            self.stream.start()
        except Exception as e:
            print(f"Failed to start audio stream: {e}")


    def stop_audio_stream(self):
        """Stop the audio stream if it's running."""
        if hasattr(self, 'stream') and self.stream.active:
            self.stream.stop()

            


    def create_toggle_paths_button(self):
        """Create a compact 'Hide Paths'/'Show Paths' button and align it to the right."""
        self.toggle_paths_button = QtWidgets.QPushButton("Hide Paths")

        # Set the button to be compact
        self.toggle_paths_button.setSizePolicy(QtWidgets.QSizePolicy.Minimum, QtWidgets.QSizePolicy.Minimum)

        # Remove extra padding/margins and make font size smaller
        self.toggle_paths_button.setStyleSheet("""
            QPushButton {
                padding: 3px 8px;
                font-size: 12px;
                color: white;
                background-color: #444444;  /* Dark gray */
            }
            QPushButton:hover {
                background-color: #555555;  /* Slightly lighter gray on hover */
            }
        """)

        # Align the button to the right
        toggle_paths_layout = QtWidgets.QHBoxLayout()
        toggle_paths_layout.addStretch()  # Push the button to the right
        toggle_paths_layout.addWidget(self.toggle_paths_button, alignment=QtCore.Qt.AlignRight)

        # Connect the button click to the toggle function
        self.toggle_paths_button.clicked.connect(self.toggle_paths_section)

        # Add the layout with the button to the main layout
        self.main_layout.addLayout(toggle_paths_layout)


    def init_ui(self):
        """Initialize and set up the UI components."""
        self.setWindowTitle("ALTTPR Seed Generator")
        self.setGeometry(100, 100, 1000, 600)  # Adjusted window size for more space

        # Create the menu bar
        self.create_menus()

        # Central widget
        central_widget = QtWidgets.QWidget()
        self.setCentralWidget(central_widget)

        # Main layout for the central widget
        self.main_layout = QtWidgets.QVBoxLayout(central_widget)

        # Add audio controls early
        self.create_audio_controls()

        # Create the "Paths and Presets" section
        self.create_paths_and_presets()

        # Create buttons and actions (including checkboxes) first
        self.create_buttons()

        # Create toggle paths button
        self.create_toggle_paths_button()

        # Add the actions group box (buttons and checkboxes) to the main layout
        self.main_layout.addWidget(self.actions_groupbox)

        # Create permalink input section and info box
        self.create_permalink_input()
        self.create_info_box()

        # **Remove the following line if the visualizer is already added in create_audio_controls**
        # self.main_layout.addWidget(self.audio_visualizer)  # This line is redundant

        # Load config after UI components are initialized
        self.load_config()

        # Load presets after initializing everything, but only if the preset folder is valid
        preset_folder_path = self.path_inputs.get("preset_folder", QtWidgets.QLineEdit()).text()
        if preset_folder_path and os.path.exists(preset_folder_path):
            self.load_presets()

        self.populate_msu_combobox()
        self.stop_visualizer()

    def start_visualizer(self):
        """Start the visualizer timer when audio is playing."""
        self.start_audio_stream()  # Start capturing audio data
        #self.visualizer_timer.start(100)  # 100ms interval for smooth updates

    def stop_visualizer(self):
        """Stop the visualizer timer and audio stream when audio is paused or stopped."""
        try:
            if hasattr(self, 'visualizer_timer') and self.visualizer_timer.isActive():
                self.visualizer_timer.stop()
            if hasattr(self, 'stream') and self.stream.active:
                self.stream.stop()
        except Exception as e:
            print(f"Error while stopping visualizer: {e}")
    
    def update_visualizer(self, amplitude_data=None):
        """Update the visualizer with audio amplitude data."""
        if amplitude_data is None:
            # Provide default data if nothing is passed
            amplitude_data = np.zeros(10)
        
        self.amplitude_data = amplitude_data
        self.audio_visualizer.update()  # Trigger a repaint of the widget


    def init_mixer(self):
        """Initialize the pygame mixer for audio playback."""
        try:
            # Initialize the Pygame video system (necessary for event handling)
            pygame.display.init()

            # Initialize the mixer with 44.1kHz, 16-bit stereo
            pygame.mixer.init(frequency=44100, size=-16, channels=2)

            # Set event to trigger when a music track ends
            pygame.mixer.music.set_endevent(pygame.USEREVENT)
        except Exception as e:
            self.show_message(f"Failed to initialize audio mixer: {e}")


    def create_audio_controls(self):
        """Create audio control buttons for playback, volume, stop, and preview."""
        self.audio_control_layout = QtWidgets.QHBoxLayout()

        # Preview checkbox
        self.preview_checkbox = QtWidgets.QCheckBox("MSU Preview")
        self.preview_checkbox.setChecked(False)  # Default unchecked (not previewing)
        self.audio_control_layout.addWidget(self.preview_checkbox)

        # Previous track button
        self.prev_button = QtWidgets.QPushButton("Previous")
        self.prev_button.clicked.connect(self.play_previous_track)
        self.audio_control_layout.addWidget(self.prev_button)

        # Play button
        self.play_button = QtWidgets.QPushButton("Play")
        self.play_button.clicked.connect(self.play_audio_control)
        self.audio_control_layout.addWidget(self.play_button)

        # Pause button
        self.pause_button = QtWidgets.QPushButton("Pause")
        self.pause_button.clicked.connect(self.pause_audio_control)
        self.audio_control_layout.addWidget(self.pause_button)

        # Next track button
        self.next_button = QtWidgets.QPushButton("Next")
        self.next_button.clicked.connect(self.play_next_track)
        self.audio_control_layout.addWidget(self.next_button)

        # Stop button
        self.stop_button = QtWidgets.QPushButton("Stop")
        self.stop_button.clicked.connect(self.stop_audio)
        self.audio_control_layout.addWidget(self.stop_button)

        # Volume slider
        self.volume_slider = QtWidgets.QSlider(QtCore.Qt.Horizontal)
        self.volume_slider.setRange(0, 100)  # Volume range: 0-100%
        self.volume_slider.setValue(int(self.volume_level * 100))  # Set to current volume level
        self.volume_slider.valueChanged.connect(self.set_volume)
        self.audio_control_layout.addWidget(QtWidgets.QLabel("Volume:"))
        self.audio_control_layout.addWidget(self.volume_slider)

        self.audio_visualizer = AudioVisualizer(self)
        self.audio_visualizer.setFixedSize(150, 50)  # New size: 150x50
        self.audio_control_layout.addWidget(self.audio_visualizer)

        # Add the audio_control_layout to the main_layout
        self.main_layout.addLayout(self.audio_control_layout)
        


    
    def reset_amplitudes(self):
        """Reset the visualizer's amplitudes to zero and hide it."""
        self.target_amplitudes = np.zeros_like(self.amplitude_data)
        self.current_amplitudes = np.zeros_like(self.amplitude_data)
        self.update()  # Trigger a repaint to reflect the reset
        self.hide()    # Hide the visualizer

    def play_audio_control(self):
        """Play or resume the audio, loading WAV files if necessary."""
        if self.is_paused:
            # Resume if the track was paused
            self.start_visualizer()
            pygame.mixer.music.unpause()
            self.is_paused = False

            # Show the visualizer when resuming
            if self.audio_visualizer:
                self.audio_visualizer.show()

        elif not self.is_playing:
            # Reuse the folder validation and playlist preparation logic from `on_msu_selection_change`
            self.on_msu_selection_change()

            # After running the selection logic, check if the playlist is ready
            if not self.playlist:
                self.show_message("No MSU files loaded to play.")
                print(f"[DEBUG] No WAV files were found in {self.msu_folder}")
                return

            # Play the current track if the playlist is ready
            if self.playlist:
                self.play_audio(self.playlist[self.current_track_index])
            else:
                self.show_message("No MSU files available to play.")



    def pause_audio_control(self):
        """Pause the currently playing audio."""
        if pygame.mixer.music.get_busy():
            pygame.mixer.music.pause()
            self.is_paused = True
            self.stop_visualizer()

            # Reset the visualizer's amplitudes to prevent movement
            if self.audio_visualizer:
                self.audio_visualizer.reset_amplitudes()

    def play_previous_track(self):
        """Play the previous track in the playlist."""
        self.update_timer.stop()  # Stop the timer to avoid conflicts
        if self.playlist:
            self.stop_audio()  # Fully stop the current track
            pygame.event.clear()  # Clear any pending audio events

            # Navigate to the previous track
            if self.current_track_index > 0:
                self.current_track_index -= 1
            else:
                self.current_track_index = len(self.playlist) - 1  # Loop to the last track

            # Play the previous track without queuing the next one automatically
            self.play_audio(self.playlist[self.current_track_index], queue_next=False)
            self.update_timer.start(500)  # Restart the timer

    def play_next_track(self):
        """Play the next track in the playlist."""
        self.update_timer.stop()  # Stop the timer to avoid conflicts
        if self.playlist:
            self.stop_audio()  # Fully stop the current track
            pygame.event.clear()  # Clear any pending audio events

            # Navigate to the next track
            if self.current_track_index < len(self.playlist) - 1:
                self.current_track_index += 1
            else:
                self.current_track_index = 0  # Loop to the first track

            # Play the next track and queue the following one
            self.play_audio(self.playlist[self.current_track_index], queue_next=True)
            self.update_timer.start(500)  # Restart the timer



    def stop_audio(self):
        """Stop the audio playback and reset the current playing status."""
        try:
            if pygame.mixer.music.get_busy():
                pygame.mixer.music.stop()  # Stop playback
                pygame.event.clear()  # Clear any pending audio events
            self.is_playing = False
            self.is_paused = False
            self.stop_visualizer()

            # Stop the audio data timer
            if hasattr(self, 'audio_timer'):
                self.audio_timer.stop()

            # Reset the visualizer's amplitudes to prevent movement
            if self.audio_visualizer:
                self.audio_visualizer.reset_amplitudes()

            # Check if 'stream' exists before trying to stop it
            if hasattr(self, 'stream') and self.stream.active:
                self.stream.stop()
        except Exception as e:
            print(f"Error while stopping audio: {e}")


    def set_volume(self):
        """Adjust the volume based on slider input and save to config."""
        volume_level = self.volume_slider.value() / 100  # Convert to a range of 0.0 to 1.0
        pygame.mixer.music.set_volume(volume_level)

        # Save the volume level to the config file
        if "Audio" not in self.config:
            self.config.add_section("Audio")

        self.config["Audio"]["volume"] = str(self.volume_slider.value())  # Store the raw slider value (0-100)

        with open(self.config_file, "w") as configfile:
            self.config.write(configfile)

    def play_audio(self, file_path, queue_next=True):
        """Play audio and prepare data for visualization using dual processing."""
        if self.preview_checkbox.isChecked():
            try:
                # Initialize the mixer if it hasn't been already
                if not pygame.mixer.get_init():
                    self.init_mixer()

                # Stop any currently playing audio
                if pygame.mixer.music.get_busy():
                    pygame.mixer.music.stop()
                    pygame.event.clear()

                # Load the new WAV file
                pygame.mixer.music.load(file_path)

                # Set the volume
                volume_level = self.volume_slider.value() / 100
                pygame.mixer.music.set_volume(volume_level)

                # Play the WAV file
                pygame.mixer.music.play()

                # Mark the track as playing
                self.is_playing = True

                # Start visualizer processing
                self.process_audio_data(file_path)

                # Only queue the next track if this is an automatic progression
                if queue_next:
                    self.queue_next_track()

                # Start the visualizer timer
                self.start_visualizer()

                # Ensure the visualizer is visible when playing
                if self.audio_visualizer:
                    self.audio_visualizer.show()

            except Exception as e:
                self.show_message(f"Failed to play audio: {e}")
                self.is_playing = False  # Reset playing state on failure

    def process_audio_data(self, file_path):
        """Load and process audio data for visualization."""
        try:
            # Open the WAV file
            wf = wave.open(file_path, 'rb')
            # Extract audio parameters
            num_channels = wf.getnchannels()
            sample_width = wf.getsampwidth()
            frame_rate = wf.getframerate()
            num_frames = wf.getnframes()
            duration = num_frames / frame_rate

            # Read all frames
            raw_data = wf.readframes(num_frames)
            wf.close()

            # Convert raw data to NumPy array
            if sample_width == 2:
                dtype = np.int16
            elif sample_width == 4:
                dtype = np.int32
            else:
                dtype = np.float32  # Assuming float for other widths

            audio_data = np.frombuffer(raw_data, dtype=dtype)

            # If stereo, take mean to convert to mono
            if num_channels > 1:
                audio_data = audio_data.reshape(-1, num_channels)
                audio_data = audio_data.mean(axis=1)

            # **Remove or adjust normalization**
            # Option 1: Remove normalization
            # self.audio_data = audio_data

            # Option 2: Adjust normalization to a lower value to prevent clipping
            self.audio_data = audio_data / np.max(np.abs(audio_data)) * 0.8  # Scale to 80% of max

            # Store the audio data and frame rate
            self.frame_rate = frame_rate

            # Start a timer to feed amplitude data to the visualizer
            self.audio_position = 0
            self.audio_timer = QtCore.QTimer()
            self.audio_timer.timeout.connect(self.update_visualizer_with_audio)
            self.audio_timer.start(30)  # Update every 30 ms (~33 FPS)

        except Exception as e:
            self.show_message(f"Failed to process audio data: {e}")

    def update_visualizer_with_audio(self):
        """Update the visualizer with actual audio amplitude data using FFT."""
        if not hasattr(self, 'audio_data'):
            return

        # Define the window size for amplitude calculation
        window_size = int(0.03 * self.frame_rate)  # 30ms window

        if self.audio_position + window_size > len(self.audio_data):
            # Stop the timer if we've reached the end of the audio data
            self.audio_timer.stop()

            # Reset the visualizer's amplitudes to zero
            if self.audio_visualizer:
                self.audio_visualizer.reset_amplitudes()
            return

        # Extract the current window of audio data
        window_data = self.audio_data[self.audio_position:self.audio_position + window_size]
        self.audio_position += window_size

        # **Compute FFT to get frequency components**
        fft_result = np.fft.rfft(window_data)
        fft_magnitude = np.abs(fft_result)

        # **Define frequency bands based on the number of visualizer bars**
        num_bars = len(self.audio_visualizer.amplitude_data)
        freq_bins = np.linspace(0, self.frame_rate / 2, num_bars + 1)  # Nyquist frequency

        # **Initialize an array to hold amplitude for each bar**
        bar_amplitudes = np.zeros(num_bars)

        # **Distribute FFT magnitudes into frequency bands**
        for i in range(num_bars):
            # Define the frequency range for the current bar
            start_freq = freq_bins[i]
            end_freq = freq_bins[i + 1]

            # Find indices of FFT results that fall into this frequency range
            indices = np.where((np.fft.rfftfreq(window_size, d=1./self.frame_rate) >= start_freq) &
                            (np.fft.rfftfreq(window_size, d=1./self.frame_rate) < end_freq))[0]

            if len(indices) > 0:
                # Compute the average magnitude for this frequency band
                bar_amplitudes[i] = np.mean(fft_magnitude[indices])
            else:
                bar_amplitudes[i] = 0

        # **Normalize bar amplitudes to prevent excessive scaling**
        max_amplitude = np.max(bar_amplitudes)
        if max_amplitude > 0:
            bar_amplitudes = bar_amplitudes / max_amplitude

        # **Emit the normalized amplitudes to the visualizer**
        if self.audio_visualizer:
            self.audio_visualizer.amplitude_signal.emit(bar_amplitudes)



    def queue_next_track(self):
        """Queue the next track in the playlist after the current one finishes."""
        next_track_index = self.current_track_index + 1
        if next_track_index < len(self.playlist):
            pygame.mixer.music.queue(self.playlist[next_track_index])



    def show_message(self, message):
        """Helper function to show a message box."""
        QtWidgets.QMessageBox.information(self, "Information", message)

    def on_msu_selection_change(self):
        """Handle when a new MSU pack is selected."""
        # Check if the config is still loading or the MSU packs are still refreshing to avoid premature execution
        if self.loading_config:
            return  # Exit early if the configuration is still loading

        selected_msu_pack = self.msu_combobox.currentText()

        # Exit early if 'Random' is selected
        if selected_msu_pack == "Random":
            return  # Do nothing if 'Random' is selected

        # Retrieve the MSU folder from the path input
        msu_root_folder = self.path_inputs["msu_folder"].text()
        if not msu_root_folder or not os.path.exists(msu_root_folder):
            self.show_message("MSU folder is not valid. Please check the folder path.")
            return

        msu_folder = os.path.join(msu_root_folder, selected_msu_pack)

        # Check if a valid MSU pack folder was selected
        if not selected_msu_pack:
            self.show_message("No MSU pack selected; proceeding without MSU support.")
            return

        # Store msu_folder as an attribute for later use
        self.msu_folder = msu_folder

        # Stop audio and clear any Pygame events
        self.stop_audio()
        pygame.event.clear()

        # Reset the playlist and track index
        self.playlist = []
        self.current_track_index = 0

        # If the selected MSU folder exists, prepare the playlist
        if os.path.isdir(msu_folder):
            self.prepare_msu_playlist(msu_folder)

            if self.playlist:
                # Start playing the first track if a playlist is prepared
                self.play_audio(self.playlist[self.current_track_index])
            else:
                self.show_message(f"No audio files found in {msu_folder}.")
        else:
            self.show_message(f"Invalid MSU pack folder: {msu_folder}")







    def prepare_msu_playlist(self, msu_folder):
        """Prepare the playlist from the MSU folder by gathering .wav files and ensuring proper track order."""
        try:
            # Clear or initialize the playlist before scanning
            self.playlist = []

            # Gather all the WAV files from the MSU pack folder
            wav_files = [os.path.join(msu_folder, f) for f in os.listdir(msu_folder) if f.endswith('.wav')]

            # If no WAV files are found, attempt to convert PCM files to WAV
            if not wav_files:
                print("No WAV files found, converting PCM files...")
                conversion_successful = self.convert_additional_pcm_to_wav(msu_folder)
                if not conversion_successful:
                    self.show_message("No WAV files and PCM conversion failed.")
                    return

                # Gather newly converted WAV files after PCM conversion
                wav_files = [os.path.join(msu_folder, f) for f in os.listdir(msu_folder) if f.endswith('.wav')]

            # Sort the playlist based on the track number in the filename (using regex to extract the number)
            def extract_track_number(file_name):
                match = re.search(r'-(\d+)\.wav$', file_name)
                return int(match.group(1)) if match else float('inf')  # Handle non-numbered files gracefully

            self.playlist = sorted(wav_files, key=extract_track_number)

            # Debugging: Print out the playlist to ensure correct ordering
            print(f"MSU Playlist: {self.playlist}")

            # Reset the current track index to 0
            self.current_track_index = 0

        except Exception as e:
            self.show_message(f"Error preparing MSU playlist: {e}")


    def check_next_track(self):
        """Check if the current track has ended and play the next one."""
        for event in pygame.event.get():
            if event.type == pygame.USEREVENT:  # Event triggered when a track finishes
                self.play_next_track()

                # Reset the visualizer's amplitudes after the track ends
                if self.audio_visualizer:
                    self.audio_visualizer.reset_amplitudes()


    def convert_additional_pcm_to_wav(self, msu_folder):
        """Convert additional PCM files to WAV if no more WAV files are found."""
        try:
            pcm_files = [f for f in os.listdir(msu_folder) if f.endswith('.pcm')]

            if not pcm_files:
                print("No PCM files found to convert.")
                return False

            converted_files = []
            for pcm_file in pcm_files:
                wav_file_path = os.path.join(msu_folder, pcm_file.replace(".pcm", ".wav"))
                if not os.path.exists(wav_file_path):
                    pcm_file_path = os.path.join(msu_folder, pcm_file)
                    converted_wav = self.convert_pcm_to_wav(pcm_file_path)
                    if converted_wav:
                        converted_files.append(converted_wav)
                        # Add the newly converted file to the playlist
                        print(f"Converted PCM file {pcm_file} to WAV as {converted_wav}")

            return len(converted_files) > 0

        except Exception as e:
            self.show_message(f"Error converting PCM files: {e}")
            return False


    def convert_pcm_to_wav(self, pcm_file_path):
        """Convert a PCM file to WAV using pydub and return the path of the WAV file."""
        try:
            # Define the output WAV file path
            wav_file_path = pcm_file_path.replace(".pcm", ".wav")

            # Use pydub to read the raw PCM data and convert it to WAV
            pcm_audio = AudioSegment.from_file(pcm_file_path, format="raw", sample_width=2, frame_rate=44100, channels=2)
            pcm_audio.export(wav_file_path, format="wav")

            return wav_file_path
        except Exception as e:
            self.show_message(f"Failed to convert PCM to WAV: {e}")
            return None

    
    def load_sprites(self):
        """Load the spritesheet and sprite data for the app."""
        try:
            # Load the sprite sheet
            spritesheet_url = "https://alttpr-assets.s3.us-east-2.amazonaws.com/sprites.31.2.png"
            headers = {'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36'}
            response = requests.get(spritesheet_url, headers=headers)
            response.raise_for_status()
            image_data = response.content
            self.spritesheet = QtGui.QPixmap()
            self.spritesheet.loadFromData(image_data)

            # Fetch sprite data
            response = requests.get('https://alttpr.com/sprites')
            response.raise_for_status()
            self.sprite_data = response.json()


        except requests.RequestException as e:
            print(f"[DEBUG] Error loading sprite sheet or sprite data: {e}")



    def browse_msu_folder(self):
        """Open a dialog to select an MSU folder."""
        msu_folder = QtWidgets.QFileDialog.getExistingDirectory(self, "Select MSU Folder")
        
        if msu_folder:
            # Set the selected folder in the field
            self.msu_field.setText(msu_folder)
            # Optionally, you can also validate the folder here (check for MSU/PCM files)
            valid, message = self.validate_msu_folder(msu_folder)
            if not valid:
                QtWidgets.QMessageBox.warning(self, "Invalid MSU Folder", message)





    def create_buttons(self):
        """Create buttons for customizing patches, generating seed, etc., along with action checkboxes."""
        self.actions_groupbox = QtWidgets.QGroupBox("Actions")
        actions_layout = QtWidgets.QVBoxLayout()

        # Add preset selection layout to the actions layout
        preset_selection_layout = self.create_preset_selection()
        actions_layout.addLayout(preset_selection_layout)

        # Add checkboxes for actions
        self.patch_checkbox = QtWidgets.QCheckBox("Patch ROM after Generating")
        self.launch_emulator_checkbox = QtWidgets.QCheckBox("Launch Emulator")
        self.launch_emotracker_checkbox = QtWidgets.QCheckBox("Launch EmoTracker")

        # Horizontal layout for MSU checkbox, ComboBox, and Refresh Button with reduced spacing
        msu_options_layout = QtWidgets.QHBoxLayout()
        msu_options_layout.setSpacing(5)  # Reduce spacing between elements

        # Add new checkbox for MSU support
        self.use_msu_checkbox = QtWidgets.QCheckBox("Use MSU Soundtrack")  # New checkbox for MSU
        self.use_msu_checkbox.setToolTip("Enable this option to use an MSU soundtrack if available.")
        
        # Add MSU ComboBox
        self.msu_combobox = QtWidgets.QComboBox()
        self.msu_combobox.setToolTip("Select the MSU pack to use or choose 'Random'")
        self.msu_combobox.setFixedWidth(150)  # Set width to make the ComboBox smaller
        self.msu_combobox.addItem("Random")  # Add 'Random' option as the first entry
        

        # Add Refresh Button
        self.refresh_msu_button = QtWidgets.QPushButton("Refresh")
        self.refresh_msu_button.setFixedSize(60, 40)  # Small refresh button
        self.refresh_msu_button.setToolTip("Refresh the list of available MSU packs")
        self.refresh_msu_button.clicked.connect(self.populate_msu_combobox)  # Connect button to refresh method

        # Add widgets to the MSU layout
        msu_options_layout.addWidget(self.use_msu_checkbox)  # Add MSU checkbox first
        msu_options_layout.addWidget(self.msu_combobox)  # Add ComboBox next
        msu_options_layout.addWidget(self.refresh_msu_button)  # Add Refresh Button last

        # Create a layout for the checkboxes and add them
        checkboxes_layout = QtWidgets.QVBoxLayout()
        checkboxes_layout.addWidget(self.patch_checkbox)
        checkboxes_layout.addWidget(self.launch_emulator_checkbox)
        checkboxes_layout.addWidget(self.launch_emotracker_checkbox)
        checkboxes_layout.addLayout(msu_options_layout)  # Add MSU layout (checkbox + combo + button)

        # Connect checkbox state changes to save_config
        self.patch_checkbox.stateChanged.connect(self.save_config)
        self.launch_emulator_checkbox.stateChanged.connect(self.save_config)
        self.launch_emotracker_checkbox.stateChanged.connect(self.save_config)
        self.use_msu_checkbox.stateChanged.connect(self.save_config)
        self.msu_combobox.currentIndexChanged.connect(self.save_config)  # Save MSU selection
        self.msu_combobox.currentIndexChanged.connect(self.on_msu_selection_change)

        # Add checkboxes layout to the actions layout
        actions_layout.addLayout(checkboxes_layout)

        # Create a layout for the buttons
        button_layout = QtWidgets.QHBoxLayout()
        self.customize_patch_button = QtWidgets.QPushButton("Customize Patch")
        self.customize_patch_button.clicked.connect(self.open_customize_patch_dialog)

        self.generate_button = QtWidgets.QPushButton("Generate Seed")
        self.generate_button.clicked.connect(self.generate_seed)

        self.fetch_daily_seed_button = QtWidgets.QPushButton("Fetch Daily Seed")
        self.fetch_daily_seed_button.clicked.connect(self.fetch_daily_seed)

        self.seed_history_button = QtWidgets.QPushButton("Seed History")
        self.seed_history_button.clicked.connect(self.open_seed_history_dialog)

        # Add buttons to the button layout
        button_layout.addWidget(self.customize_patch_button)
        button_layout.addWidget(self.generate_button)
        button_layout.addWidget(self.fetch_daily_seed_button)
        button_layout.addWidget(self.seed_history_button)  # Add seed history button here

        # Create a new layout to organize the overall content
        main_actions_layout = QtWidgets.QHBoxLayout()

        # Create a vertical layout for checkboxes and buttons
        left_layout = QtWidgets.QVBoxLayout()
        left_layout.addLayout(actions_layout)
        left_layout.addLayout(button_layout)

        # Add the left layout to the main actions layout (for checkboxes and buttons)
        main_actions_layout.addLayout(left_layout)

        # Add sprite display label to the right of the buttons, above everything
        self.sprite_display_label_in_actions.setFixedSize(128, 128)  # Increased the size of the sprite display for better visibility
        self.sprite_display_label_in_actions.setAlignment(QtCore.Qt.AlignRight | QtCore.Qt.AlignTop)
        main_actions_layout.addWidget(self.sprite_display_label_in_actions)

        # Set the main layout for the actions group box
        self.actions_groupbox.setLayout(main_actions_layout)

    def create_menus(self):
        """Create the menu bar with menus and actions."""
        # Create the menu bar
        menu_bar = self.menuBar()

        # --------------------
        # File Menu
        # --------------------
        file_menu = menu_bar.addMenu("File")


        # Save Action
        save_action = QtWidgets.QAction("Save", self)
        save_action.setShortcut("Ctrl+S")
        save_action.setStatusTip("Save current settings")
        save_action.triggered.connect(self.save_settings)
        file_menu.addAction(save_action)

        # Exit Action
        exit_action = QtWidgets.QAction("Exit", self)
        exit_action.setShortcut("Ctrl+Q")
        exit_action.setStatusTip("Exit the application")
        exit_action.triggered.connect(self.close)
        file_menu.addAction(exit_action)

        # --------------------
        # Edit Menu
        # --------------------
        edit_menu = menu_bar.addMenu("Edit")

        # Preferences Action
        preferences_action = QtWidgets.QAction("Preferences", self)
        preferences_action.setShortcut("Ctrl+,")
        preferences_action.setStatusTip("Edit application preferences")
        preferences_action.triggered.connect(self.open_preferences)
        edit_menu.addAction(preferences_action)

        # --------------------
        # Help Menu
        # --------------------
        help_menu = menu_bar.addMenu("Help")

        # About Action
        about_action = QtWidgets.QAction("About", self)
        about_action.setStatusTip("About this application")
        about_action.triggered.connect(self.show_about_dialog)
        help_menu.addAction(about_action)

    def open_preferences(self):
        """Open a preferences dialog."""
        dialog = QtWidgets.QDialog(self)
        dialog.setWindowTitle("Preferences")
        dialog.setModal(True)
        layout = QtWidgets.QVBoxLayout(dialog)
        
        # --- Theme Selection ---
        theme_layout = QtWidgets.QHBoxLayout()
        theme_label = QtWidgets.QLabel("Select Theme:")
        self.theme_combo = QtWidgets.QComboBox()
        self.theme_combo.addItems(["Nightwave", "Light", "Dark", "Blue", "Synthwave", "Zelda"])  # Available themes
        current_theme = self.config.get("Settings", "theme", fallback="Dark")
        index = self.theme_combo.findText(current_theme, QtCore.Qt.MatchFixedString)
        if index >= 0:
            self.theme_combo.setCurrentIndex(index)
        theme_layout.addWidget(theme_label)
        theme_layout.addWidget(self.theme_combo)
        layout.addLayout(theme_layout)
        
        # --- OK and Cancel Buttons ---
        buttons = QtWidgets.QDialogButtonBox(
            QtWidgets.QDialogButtonBox.Ok | QtWidgets.QDialogButtonBox.Cancel,
            QtCore.Qt.Horizontal,
            dialog
        )
        buttons.accepted.connect(dialog.accept)
        buttons.rejected.connect(dialog.reject)
        layout.addWidget(buttons)
        
        if dialog.exec_() == QtWidgets.QDialog.Accepted:
            selected_theme = self.theme_combo.currentText()
            self.current_theme = selected_theme  # Store as an instance variable
            self.apply_theme(selected_theme)
            # Save the selected theme to config
            if "Settings" not in self.config:
                self.config.add_section("Settings")
            self.config["Settings"]["theme"] = selected_theme
            # Instead of writing directly here, call save_config
            self.save_config()

    def apply_theme(self, theme_name):
        """Apply the selected theme to the application."""
        themes = {
            "Light": {
                "stylesheet": f"""
                    /* Light Theme */
                    QMainWindow {{
                        background-color: #f0f0f0;
                        font-family: '{self.font_family}';  /* Custom font */
                    }}

                    QWidget {{
                        background-color: #f0f0f0;
                        color: #000000;  /* General text color */
                        font-family: '{self.font_family}';  /* Custom font */
                    }}

                    /* Explicitly set text color for specific widgets */
                    QLabel, QLineEdit, QComboBox, QCheckBox, QRadioButton, QPushButton, QListWidget, QDialog, QDialogButtonBox, QTabWidget {{
                        color: #000000;  /* Ensure all text is black */
                        font-family: '{self.font_family}';  /* Custom font */
                    }}

                    QPushButton {{
                        background-color: #ffffff;
                        border: 2px solid #8f8f91;
                        border-radius: 5px;
                        padding: 5px;
                        color: #000000;  /* Ensure button text is black */
                        font-family: '{self.font_family}';  /* Custom font */
                    }}

                    QPushButton:hover {{
                        background-color: #e6e6e6;
                    }}

                    QMenuBar {{
                        background-color: #e0e0e0;
                    }}

                    QMenuBar::item {{
                        background: transparent;
                        padding: 5px 10px;
                        color: #000000;  /* Ensure menu bar items are black */
                    }}

                    QMenuBar::item:selected {{
                        background-color: #d0d0d0;
                        color: #000000;  /* Ensure selected menu bar items are black */
                    }}

                    QMenu {{
                        background-color: #ffffff;
                        border: 1px solid #8f8f91;
                        color: #000000;  /* Ensure menu text is black */
                    }}

                    QMenu::item {{
                        color: #000000;  /* Ensure menu items are black */
                    }}

                    QMenu::item:selected {{
                        background-color: #d0d0d0;
                        color: #000000;  /* Ensure selected menu items are black */
                    }}

                    QCheckBox {{
                        color: #000000;  /* Ensure checkbox text is black */
                    }}

                    QRadioButton {{
                        color: #000000;  /* Ensure radio button text is black */
                    }}

                    /* Style QListWidget */
                    QListWidget {{
                        background-color: #ffffff;
                        border: 1px solid #8f8f91;
                        color: #000000;  /* Ensure list items are black */
                    }}

                    QListWidget::item {{
                        padding: 5px;
                        color: #000000;  /* Ensure list item text is black */
                    }}

                    QListWidget::item:selected {{
                        background-color: #d0d0d0;
                        color: #000000;  /* Ensure selected list item text is black */
                    }}

                    /* Style QDialog and its components */
                    QDialog {{
                        background-color: #f0f0f0;
                        color: #000000;
                        font-family: '{self.font_family}';  /* Custom font */
                    }}

                    QDialogButtonBox QPushButton {{
                        background-color: #ffffff;
                        border: 2px solid #8f8f91;
                        border-radius: 5px;
                        padding: 5px;
                        color: #000000;  /* Ensure dialog buttons have black text */
                        font-family: '{self.font_family}';  /* Custom font */
                    }}

                    QDialogButtonBox QPushButton:hover {{
                        background-color: #e6e6e6;
                    }}

                    /* Style QTabWidget if used */
                    QTabWidget::pane {{
                        border: 1px solid #8f8f91;
                    }}

                    QTabBar::tab {{
                        background: #ffffff;
                        border: 1px solid #8f8f91;
                        padding: 5px;
                        color: #000000;  /* Ensure tab text is black */
                        font-family: '{self.font_family}';  /* Custom font */
                    }}

                    QTabBar::tab:selected {{
                        background: #d0d0d0;
                        color: #000000;  /* Ensure selected tab text is black */
                    }}

                    /* Styles for path input boxes */
                    QLineEdit#preset_folder_input,
                    QLineEdit#output_folder_input,
                    QLineEdit#rom_path_input,
                    QLineEdit#retroarch_path_input,
                    QLineEdit#core_path_input,
                    QLineEdit#emotracker_path_input,
                    QLineEdit#snes9x_path_input,
                    QLineEdit#msu_folder_input {{
                        border: 1px solid #a0a0a0;       /* Subdued Gray Border */
                        border-radius: 4px;              /* Rounded Corners */
                        padding: 5px;                     /* Inner Padding */
                        background-color: #ffffff;       /* White Background */
                        color: #000000;                   /* Black Text */
                        font-family: '{self.font_family}';  /* Custom Font */
                    }}

                    QLineEdit#preset_folder_input:hover,
                    QLineEdit#output_folder_input:hover,
                    QLineEdit#rom_path_input:hover,
                    QLineEdit#retroarch_path_input:hover,
                    QLineEdit#core_path_input:hover,
                    QLineEdit#emotracker_path_input:hover,
                    QLineEdit#snes9x_path_input:hover,
                    QLineEdit#msu_folder_input:hover {{
                        border: 1px solid #737373;       /* Slightly Lighter Gray on Hover */
                    }}

                    QLineEdit#preset_folder_input:focus,
                    QLineEdit#output_folder_input:focus,
                    QLineEdit#rom_path_input:focus,
                    QLineEdit#retroarch_path_input:focus,
                    QLineEdit#core_path_input:focus,
                    QLineEdit#emotracker_path_input:focus,
                    QLineEdit#snes9x_path_input:focus,
                    QLineEdit#msu_folder_input:focus {{
                        border: 1px solid #00BCD4;       /* Bright Cyan Border on Focus */
                        background-color: #e0f7fa;       /* Light Cyan Background on Focus */
                        color: #000000;                   /* Black Text on Focus */
                    }}

                    /* Specific style for seed info widget */
                    /* Replace 'seedInfoLabel' with your actual objectName */
                    QLabel#seedInfoLabel, QTextBrowser#seedInfoBrowser {{
                        color: #333333;  /* Dark Gray for general text */
                        font-family: '{self.font_family}';  /* Ensure consistent font */
                    }}

                /* Add styles for headers inside the seed info widget */
                QTextBrowser#seedInfoBrowser h1, QTextBrowser#seedInfoBrowser h2, QTextBrowser#seedInfoBrowser h3 {{
                    color: #0077cc;  /* Cool Blue color for headers */
                    font-weight: bold;
                }}
                """,
                "visualizer_colors": {
                    "top": QtGui.QColor(255, 69, 0),    # OrangeRed
                    "bottom": QtGui.QColor(30, 144, 255)  # DodgerBlue
                }, "header_color": "#0077cc"  # Cool Blue
            },

            "Blue": {
                "stylesheet": f"""
                    /* Enhanced Grayish Blue Theme */
                    QMainWindow {{
                        background-color: #37474F;  /* Dark Slate Blue Background */
                        font-family: '{self.font_family}';  /* Custom font */
                    }}

                    QWidget {{
                        background-color: #37474F;  /* Dark Slate Blue Background */
                        color: #E0E0E0;  /* Light Gray Text */
                        font-family: '{self.font_family}';
                    }}

                    QPushButton {{
                        background-color: #455A64;  /* Steel Blue */
                        border: 2px solid #263238;  /* Charcoal Blue Border */
                        border-radius: 5px;
                        padding: 5px;
                        color: #FFFFFF;  /* White Text */
                        font-family: '{self.font_family}';
                    }}

                    QPushButton:hover {{
                        background-color: #37474F;  /* Darker Slate Blue on Hover */
                    }}

                    QMenuBar {{
                        background-color: #455A64;  /* Steel Blue */
                    }}

                    QMenuBar::item {{
                        background: transparent;
                        padding: 5px 10px;
                    }}

                    QMenuBar::item:selected {{
                        background-color: #607D8B;  /* Cool Gray Blue on Selection */
                        color: #FFFFFF;  /* White Text for Selected Item */
                    }}

                    QMenu {{
                        background-color: #455A64;  /* Steel Blue */
                        border: 1px solid #263238;  /* Charcoal Blue Border */
                        color: #FFFFFF;  /* White Text */
                    }}

                    QMenu::item {{
                        padding: 5px 20px;
                        color: #FFFFFF;  /* White Text */
                    }}

                    QMenu::item:selected {{
                        background-color: #607D8B;  /* Cool Gray Blue on Selection */
                        color: #FFFFFF;  /* White Text */
                    }}

                    /* Additional Styling for Dialogs and Other Widgets */

                    QDialog {{
                        background-color: #37474F;  /* Dark Slate Blue */
                        color: #E0E0E0;             /* Light Gray Text */
                        font-family: '{self.font_family}';
                    }}

                    QDialogButtonBox QPushButton {{
                        background-color: #455A64;  /* Steel Blue */
                        border: 2px solid #263238;  /* Charcoal Blue Border */
                        border-radius: 5px;
                        padding: 5px;
                        color: #FFFFFF;              /* White Text */
                        font-family: '{self.font_family}';
                    }}

                    QDialogButtonBox QPushButton:hover {{
                        background-color: #37474F;  /* Darker Slate Blue on Hover */
                    }}

                    /* Style QTabWidget if used */
                    QTabWidget::pane {{
                        border: 1px solid #263238;  /* Charcoal Blue Border */
                    }}

                    QTabBar::tab {{
                        background: #455A64;        /* Steel Blue */
                        border: 1px solid #263238;  /* Charcoal Blue Border */
                        padding: 5px;
                        color: #FFFFFF;             /* White Text */
                        font-family: '{self.font_family}';
                    }}

                    QTabBar::tab:selected {{
                        background: #607D8B;        /* Cool Gray Blue */
                        color: #FFFFFF;             /* White Text for Selected Tab */
                    }}

                    /* QTextBrowser Styling */
                    QTextBrowser#seedHistoryTextBrowser {{
                        background-color: #455A64;  /* Steel Blue */
                        color: #E0E0E0;             /* Light Gray Text */
                        font-family: '{self.font_family}';
                        border: 1px solid #263238;  /* Charcoal Blue Border */
                        padding: 10px;
                        border-radius: 4px;
                    }}

                    QTextBrowser#seedHistoryTextBrowser a {{
                        color: #607D8B;  /* Cool Gray Blue Links */
                        text-decoration: none;
                    }}

                    QTextBrowser#seedHistoryTextBrowser a:hover {{
                        text-decoration: underline;
                    }}

                    /* Styles for path input boxes */
                    QLineEdit#preset_folder_input,
                    QLineEdit#output_folder_input,
                    QLineEdit#rom_path_input,
                    QLineEdit#retroarch_path_input,
                    QLineEdit#core_path_input,
                    QLineEdit#emotracker_path_input,
                    QLineEdit#snes9x_path_input,
                    QLineEdit#msu_folder_input {{
                        border: 1px solid #a0a0a0;       /* Subdued Gray Border */
                        border-radius: 4px;              /* Rounded Corners */
                        padding: 5px;                     /* Inner Padding */
                        background-color: #FFFFFF;       /* White Background */
                        color: #000000;                   /* Black Text */
                        font-family: '{self.font_family}';  /* Custom Font */

                    }}

                    QLineEdit#preset_folder_input:hover,
                    QLineEdit#output_folder_input:hover,
                    QLineEdit#rom_path_input:hover,
                    QLineEdit#retroarch_path_input:hover,
                    QLineEdit#core_path_input:hover,
                    QLineEdit#emotracker_path_input:hover,
                    QLineEdit#snes9x_path_input:hover,
                    QLineEdit#msu_folder_input:hover {{
                        border: 1px solid #737373;       /* Slightly Lighter Gray on Hover */
                    }}

                    QLineEdit#preset_folder_input:focus,
                    QLineEdit#output_folder_input:focus,
                    QLineEdit#rom_path_input:focus,
                    QLineEdit#retroarch_path_input:focus,
                    QLineEdit#core_path_input:focus,
                    QLineEdit#emotracker_path_input:focus,
                    QLineEdit#snes9x_path_input:focus,
                    QLineEdit#msu_folder_input:focus {{
                        border: 1px solid #00BCD4;       /* Bright Cyan Border on Focus */
                        background-color: #e0f7fa;       /* Light Cyan Background on Focus */
                        color: #000000;                   /* Black Text on Focus */
                    }}
                """,
                "visualizer_colors": {
                    "top": QtGui.QColor(255, 69, 0),    # OrangeRed
                    "bottom": QtGui.QColor(30, 144, 255)  # DodgerBlue
                }, "header_color": "#4fc3f7" #(Lighter Cyan)
            },

            "Synthwave": {
                "stylesheet": f"""
                    /* Synthwave Theme */
                    QMainWindow {{
                        background-color: #0F1626;  /* Dark Navy Background */
                        font-family: '{self.font_family}';  /* Custom Font */
                    }}

                    QWidget {{
                        background-color: #0F1626;  /* Dark Navy Background */
                        color: #ECF0F1;  /* Light Gray Text */
                        font-family: '{self.font_family}';
                    }}

                    QPushButton {{
                        background-color: #9B59B6;  /* Neon Purple */
                        border: 2px solid #34495E;  /* Deep Blue Border */
                        border-radius: 8px;
                        padding: 10px 20px;
                        color: #FFFFFF;  /* White Text */
                        font-family: '{self.font_family}';
                    }}

                    QPushButton:hover {{
                        background-color: #A569BD;  /* Lighter Neon Purple on Hover */
                        border-color: #00BCD4;      /* Bright Cyan Border on Hover */
                    }}

                    QMenuBar {{
                        background-color: #1E1F26;  /* Space Blue Menu Bar */
                    }}

                    QMenuBar::item {{
                        background: transparent;
                        padding: 10px 20px;
                    }}

                    QMenuBar::item:selected {{
                        background-color: #E91E63;  /* Electric Pink on Selection */
                        color: #FFFFFF;              /* White Text for Selected Item */
                    }}

                    QMenu {{
                        background-color: #1E1F26;  /* Space Blue */
                        border: 1px solid #34495E;  /* Deep Blue Border */
                        color: #FFFFFF;  /* White Text */
                    }}

                    QMenu::item {{
                        padding: 10px 30px;
                        color: #FFFFFF;  /* White Text */
                    }}

                    QMenu::item:selected {{
                        background-color: #00BCD4;  /* Bright Cyan on Selection */
                        color: #000000;             /* Black Text for Selected Item */
                    }}

                    /* Dialog Styling */
                    QDialog {{
                        background-color: #0F1626;  /* Dark Navy */
                        color: #ECF0F1;             /* Light Gray Text */
                        font-family: '{self.font_family}';
                    }}

                    QDialogButtonBox QPushButton {{
                        background-color: #9B59B6;  /* Neon Purple */
                        border: 2px solid #34495E;  /* Deep Blue Border */
                        border-radius: 8px;
                        padding: 10px 20px;
                        color: #FFFFFF;  /* White Text */
                        font-family: '{self.font_family}';
                    }}

                    QDialogButtonBox QPushButton:hover {{
                        background-color: #A569BD;  /* Lighter Neon Purple on Hover */
                        border-color: #00BCD4;      /* Bright Cyan Border on Hover */
                    }}

                    /* Tab Widget Styling */
                    QTabWidget::pane {{
                        border: 1px solid #34495E;  /* Deep Blue Border */
                    }}

                    QTabBar::tab {{
                        background: #1E1F26;        /* Space Blue */
                        border: 1px solid #34495E;  /* Deep Blue Border */
                        padding: 10px 20px;
                        color: #FFFFFF;             /* White Text */
                        font-family: '{self.font_family}';
                    }}

                    QTabBar::tab:selected {{
                        background: #E91E63;        /* Electric Pink */
                        color: #FFFFFF;             /* White Text for Selected Tab */
                    }}

                    /* QTextBrowser Styling */
                    QTextBrowser#seedHistoryTextBrowser {{
                        background-color: #1E1F26;  /* Space Blue */
                        color: #ECF0F1;             /* Light Gray Text */
                        font-family: '{self.font_family}';
                        border: 1px solid #34495E;  /* Deep Blue Border */
                        padding: 10px;
                        border-radius: 4px;
                    }}

                    QTextBrowser#seedHistoryTextBrowser a {{
                        color: #00BCD4;  /* Bright Cyan Links */
                        text-decoration: none;
                    }}

                    QTextBrowser#seedHistoryTextBrowser a:hover {{
                        text-decoration: underline;
                        color: #FF4081;  /* Hot Magenta on Hover */
                    }}

                    /* Styles for path input boxes */
                    QLineEdit#preset_folder_input,
                    QLineEdit#output_folder_input,
                    QLineEdit#rom_path_input,
                    QLineEdit#retroarch_path_input,
                    QLineEdit#core_path_input,
                    QLineEdit#emotracker_path_input,
                    QLineEdit#snes9x_path_input,
                    QLineEdit#msu_folder_input {{
                        border: 1px solid #a0a0a0;       /* Subdued Gray Border */
                        border-radius: 4px;              /* Rounded Corners */
                        padding: 5px;                     /* Inner Padding */
                        background-color: #2C3E50;       /* Dark Background */
                        color: #ECF0F1;                   /* Light Gray Text */
                        font-family: '{self.font_family}';  /* Custom Font */
 
                    }}

                    QLineEdit#preset_folder_input:hover,
                    QLineEdit#output_folder_input:hover,
                    QLineEdit#rom_path_input:hover,
                    QLineEdit#retroarch_path_input:hover,
                    QLineEdit#core_path_input:hover,
                    QLineEdit#emotracker_path_input:hover,
                    QLineEdit#snes9x_path_input:hover,
                    QLineEdit#msu_folder_input:hover {{
                        border: 1px solid #737373;       /* Slightly Lighter Gray on Hover */
                    }}

                    QLineEdit#preset_folder_input:focus,
                    QLineEdit#output_folder_input:focus,
                    QLineEdit#rom_path_input:focus,
                    QLineEdit#retroarch_path_input:focus,
                    QLineEdit#core_path_input:focus,
                    QLineEdit#emotracker_path_input:focus,
                    QLineEdit#snes9x_path_input:focus,
                    QLineEdit#msu_folder_input:focus {{
                        border: 1px solid #00BCD4;       /* Bright Cyan Border on Focus */
                        background-color: #e0f7fa;       /* Light Cyan Background on Focus */
                        color: #000000;                   /* Black Text on Focus */
                    }}
                """,
                "visualizer_colors": {
                    "top": QtGui.QColor(155, 89, 182),     # Neon Purple
                    "bottom": QtGui.QColor(0, 188, 212)   # Bright Cyan
                }, "header_color": "#0077cc"  # Cool Blue
            },

            "Nightwave": {  # Updated Theme to align with Dark
                "stylesheet": f"""
                    /* Blue Nightwave Theme */
                    QMainWindow, QWidget {{
                        background-color: #1a1a1a;  /* Dark Gray Background */
                        color: #ffffff;  /* White text for better visibility */
                        font-size: 14px;
                        font-family: '{self.font_family}';  /* Custom font */
                    }}
                    QLabel, QLineEdit, QComboBox, QCheckBox, QRadioButton, QPushButton {{
                        color: #ffffff;  /* White text to ensure readability */
                        font-family: '{self.font_family}';  /* Custom font */
                    }}
                    
                    /* QPushButton */
                    QPushButton {{
                        background-color: #2b2b2b;  /* Darker Button Background */
                        border: 2px solid #4a90e2;  /* Matte blue for the button borders */
                        border-radius: 5px;          /* Rounded Corners to match Dark theme */
                        padding: 5px;                /* Inner Padding */
                        color: #ffffff;              /* White Text */
                    }}
                    QPushButton:hover {{
                        background-color: #4a90e2;   /* Matte blue hover effect */
                        color: #000000;              /* Black text when hovered */
                    }}
                    
                    /* QComboBox and QLineEdit */
                    QComboBox, QLineEdit {{
                        background-color: #2b2b2b;   /* Darker Input Field Background */
                        border: 2px solid #4a90e2;   /* Matte blue borders */
                        border-radius: 5px;          /* Rounded Corners to match Dark theme */
                        padding: 5px;                /* Inner Padding */
                        color: #ffffff;              /* White Text */
                    }}
                    QComboBox:hover, QLineEdit:hover {{
                        border: 2px solid #00BCD4;   /* Cyan Border on Hover */
                    }}
                    QComboBox:focus, QLineEdit:focus {{
                        border: 2px solid #00BCD4;   /* Bright Cyan Border on Focus */
                        background-color: #4a90e2;   /* Light Blue Background on Focus */
                        color: #000000;              /* Black Text on Focus */
                    }}

                    /* GroupBox styling */
                    QGroupBox {{
                        border: 2px solid #4a90e2;   /* Matte blue border for group box */
                        border-radius: 5px;          /* Rounded corners to match dark theme */
                        margin-top: 20px;
                        padding: 10px;               /* Adjusted padding */
                    }}
                    QGroupBox::title {{
                        subcontrol-origin: margin;
                        subcontrol-position: top left;
                        background-color: transparent;
                        color: #4a90e2;  /* Matte blue title text */
                        padding: 0 5px;
                        font-weight: bold;
                    }}

                    /* CheckBox styling */
                    QCheckBox {{
                        color: #e0e0e0;  /* Light grey text for better visibility */
                        padding: 5px;
                    }}
                    QCheckBox::indicator {{
                        width: 16px;
                        height: 16px;
                    }}
                    QCheckBox::indicator:unchecked {{
                        border: 2px solid #4a90e2;  /* Matte blue border */
                        background-color: #2b2b2b;
                    }}
                    QCheckBox::indicator:checked {{
                        border: 2px solid #4a90e2;  /* Matte blue when checked */
                        background-color: #4a90e2;
                    }}
                    
                    /* Path input boxes */
                    QLineEdit#preset_folder_input,
                    QLineEdit#output_folder_input,
                    QLineEdit#rom_path_input,
                    QLineEdit#retroarch_path_input,
                    QLineEdit#core_path_input,
                    QLineEdit#emotracker_path_input,
                    QLineEdit#snes9x_path_input,
                    QLineEdit#msu_folder_input {{
                        border: 1px solid #a0a0a0;   /* Subdued Gray Border */
                        border-radius: 4px;          /* Rounded Corners */
                        padding: 5px;                /* Inner Padding */
                        background-color: #2b2b2b;   /* Darker Background */
                        color: #ffffff;              /* White Text */
                    }}
                    QLineEdit:hover {{
                        border: 1px solid #737373;   /* Slightly Lighter Gray on Hover */
                    }}
                    QLineEdit:focus {{
                        border: 1px solid #00BCD4;   /* Bright Cyan Border on Focus */
                        background-color: #4a90e2;   /* Light Blue Background on Focus */
                        color: #000000;              /* Black Text on Focus */
                    }}
                """,
                "visualizer_colors": {
                    "top": QtGui.QColor(69, 144, 255),     # Bright Blue
                    "bottom": QtGui.QColor(0, 188, 212)    # Bright Cyan
                },
                "header_color": "#4a90e2"  # Matte Blue
            },


        "Dark": {
            "stylesheet": f"""
                /* Dark Theme */
                QMainWindow {{
                    background-color: #2c2c2c;  /* Dark Gray Background */
                    font-family: '{self.font_family}';  /* Custom font */
                }}

                QWidget {{
                    background-color: #2c2c2c;  /* Dark Gray Background */
                    color: #ffffff;  /* White Text for Contrast */
                    font-family: '{self.font_family}';  /* Custom font */
                }}

                /* Explicitly set text color for specific widgets */
                QLabel, QLineEdit, QComboBox, QCheckBox, QRadioButton, QPushButton, QListWidget, QDialog, QDialogButtonBox, QTabWidget {{
                    color: #ffffff;  /* Ensure all text is white */
                    font-family: '{self.font_family}';  /* Custom font */
                }}

                /* QPushButton Styles */
                QPushButton {{
                    background-color: #444444;  /* Darker Button Background */
                    border: 2px solid #666666;  /* Darker Border */
                    border-radius: 5px;          /* Rounded Corners */
                    padding: 5px;                /* Inner Padding */
                    color: #ffffff;              /* White Text */
                    font-family: '{self.font_family}';  /* Custom font */
                }}

                QPushButton:hover {{
                    background-color: #555555;  /* Slightly Lighter on Hover */
                }}

                /* QMenuBar Styles */
                QMenuBar {{
                    background-color: #333333;  /* Darker Menu Bar Background */
                }}

                QMenuBar::item {{
                    background: transparent;
                    padding: 5px 10px;
                    color: #ffffff;  /* White Text for Menu Items */
                }}

                QMenuBar::item:selected {{
                    background-color: #555555;  /* Highlighted Menu Item */
                    color: #ffffff;              /* White Text */
                }}

                /* QMenu Styles */
                QMenu {{
                    background-color: #444444;  /* Darker Menu Background */
                    border: 1px solid #666666;  /* Darker Border */
                    color: #ffffff;              /* White Text */
                }}

                QMenu::item {{
                    color: #ffffff;  /* White Text for Menu Items */
                }}

                QMenu::item:selected {{
                    background-color: #555555;  /* Highlighted Menu Item */
                    color: #ffffff;              /* White Text */
                }}

                /* QCheckBox and QRadioButton Styles */
                QCheckBox {{
                    color: #ffffff;  /* White Text */
                }}

                QRadioButton {{
                    color: #ffffff;  /* White Text */
                }}

                /* QListWidget Styles */
                QListWidget {{
                    background-color: #444444;  /* Darker List Background */
                    border: 1px solid #666666;  /* Darker Border */
                    color: #ffffff;              /* White Text */
                }}

                QListWidget::item {{
                    padding: 5px;
                    color: #ffffff;  /* White Text */
                }}

                QListWidget::item:selected {{
                    background-color: #555555;  /* Highlighted List Item */
                    color: #ffffff;             /* White Text */
                }}

                /* QDialog Styles */
                QDialog {{
                    background-color: #2c2c2c;  /* Dark Gray Background */
                    color: #ffffff;             /* White Text */
                    font-family: '{self.font_family}';  /* Custom font */
                }}

                /* QDialogButtonBox QPushButton Styles */
                QDialogButtonBox QPushButton {{
                    background-color: #444444;  /* Darker Button Background */
                    border: 2px solid #666666;  /* Darker Border */
                    border-radius: 5px;          /* Rounded Corners */
                    padding: 5px;                /* Inner Padding */
                    color: #ffffff;              /* White Text */
                    font-family: '{self.font_family}';  /* Custom font */
                }}

                QDialogButtonBox QPushButton:hover {{
                    background-color: #555555;  /* Slightly Lighter on Hover */
                }}

                /* QTabWidget Styles */
                QTabWidget::pane {{
                    border: 1px solid #666666;  /* Darker Border */
                }}

                QTabBar::tab {{
                    background: #444444;        /* Darker Tab Background */
                    border: 1px solid #666666;  /* Darker Border */
                    padding: 5px;
                    color: #ffffff;             /* White Text */
                    font-family: '{self.font_family}';  /* Custom font */
                }}

                QTabBar::tab:selected {{
                    background: #555555;        /* Highlighted Tab Background */
                    color: #ffffff;             /* White Text */
                }}

                /* Styles for path input boxes */
                QLineEdit#preset_folder_input,
                QLineEdit#output_folder_input,
                QLineEdit#rom_path_input,
                QLineEdit#retroarch_path_input,
                QLineEdit#core_path_input,
                QLineEdit#emotracker_path_input,
                QLineEdit#snes9x_path_input,
                QLineEdit#msu_folder_input {{
                    border: 1px solid #a0a0a0;       /* Subdued Gray Border */
                    border-radius: 4px;              /* Rounded Corners */
                    padding: 5px;                     /* Inner Padding */
                    background-color: #444444;       /* Darker Background */
                    color: #ffffff;                   /* White Text */
                    font-family: '{self.font_family}';  /* Custom Font */
                }}

                QLineEdit#preset_folder_input:hover,
                QLineEdit#output_folder_input:hover,
                QLineEdit#rom_path_input:hover,
                QLineEdit#retroarch_path_input:hover,
                QLineEdit#core_path_input:hover,
                QLineEdit#emotracker_path_input:hover,
                QLineEdit#snes9x_path_input:hover,
                QLineEdit#msu_folder_input:hover {{
                    border: 1px solid #737373;       /* Slightly Lighter Gray on Hover */
                }}

                QLineEdit#preset_folder_input:focus,
                QLineEdit#output_folder_input:focus,
                QLineEdit#rom_path_input:focus,
                QLineEdit#retroarch_path_input:focus,
                QLineEdit#core_path_input:focus,
                QLineEdit#emotracker_path_input:focus,
                QLineEdit#snes9x_path_input:focus,
                QLineEdit#msu_folder_input:focus {{
                    border: 1px solid #00BCD4;       /* Bright Cyan Border on Focus */
                    background-color: #555555;       /* Light Cyan Background on Focus */
                    color: #000000;                   /* Black Text on Focus */
                }}
            """,
            "visualizer_colors": {
                "top": QtGui.QColor(30, 144, 255),    # DodgerBlue
                "bottom": QtGui.QColor(255, 69, 0)    # OrangeRed
            },
             "header_color": "#747474 "  # Cadet Blue
            },
            "Zelda": {
        "stylesheet": f"""
            /* Zelda Theme */
            QMainWindow {{
                background-color: #494b4b;  /* Dark Slate Gray Background */
                font-family: '{self.font_family}';  /* Custom Font */
            }}

            QWidget {{
                background-color: #494b4b;  /* Dark Slate Gray Background */
                color: #ffffff;  /* White Text for Contrast */
                font-family: '{self.font_family}';  /* Custom Font */
            }}

            /* Headers and Highlighted Text */
            QLabel#header, QTextBrowser#header {{
                color: #d4ce46;  /* Golden Light */
                font-weight: bold;
                font-family: '{self.font_family}';
            }}

            /* Buttons */
            QPushButton {{
                background-color: #0e5135;  /* Deep Forest Green */
                border: 2px solid #0d9263;  /* Vibrant Emerald Green Border */
                border-radius: 8px;
                padding: 8px;
                color: #ffffff;  /* White Text */
                font-family: '{self.font_family}';  /* Custom Font */
            }}

            QPushButton:hover {{
                background-color: #0d9263;  /* Lighter Emerald Green on Hover */
                border: 2px solid #4aba91;  /* Light Seafoam Green on Hover */
            }}

            /* Menu Bar */
            QMenuBar {{
                background-color: #0e5135;  /* Deep Forest Green Menu Bar */
            }}

            QMenuBar::item {{
                background: transparent;
                padding: 5px 10px;
                color: #ffffff;  /* White Text for Menu Items */
            }}

            QMenuBar::item:selected {{
                background-color: #4aba91;  /* Light Seafoam Green on Selection */
                color: #000000;  /* Black Text for Selected Item */
            }}

            /* Menu */
            QMenu {{
                background-color: #0e5135;  /* Deep Forest Green */
                border: 1px solid #0d9263;  /* Vibrant Emerald Green Border */
                color: #ffffff;  /* White Text */
            }}

            QMenu::item {{
                padding: 5px 20px;
                color: #ffffff;  /* White Text */
            }}

            QMenu::item:selected {{
                background-color: #4aba91;  /* Light Seafoam Green on Selection */
                color: #000000;  /* Black Text */
            }}

            /* Dialog Styling */
            QDialog {{
                background-color: #494b4b;  /* Dark Slate Gray */
                color: #ffffff;  /* White Text */
                font-family: '{self.font_family}';
            }}

            /* Dialog Buttons */
            QDialogButtonBox QPushButton {{
                background-color: #0e5135;  /* Deep Forest Green */
                border: 2px solid #0d9263;  /* Vibrant Emerald Green Border */
                border-radius: 8px;
                padding: 8px;
                color: #ffffff;  /* White Text */
                font-family: '{self.font_family}';  /* Custom Font */
            }}

            QDialogButtonBox QPushButton:hover {{
                background-color: #0d9263;  /* Lighter Emerald Green on Hover */
                border: 2px solid #4aba91;  /* Light Seafoam Green on Hover */
            }}

            /* Tab Widget */
            QTabWidget::pane {{
                border: 1px solid #0d9263;  /* Vibrant Emerald Green Border */
            }}

            QTabBar::tab {{
                background: #0e5135;  /* Deep Forest Green Tab Background */
                border: 1px solid #0d9263;  /* Vibrant Emerald Green Border */
                padding: 5px;
                color: #ffffff;  /* White Text */
                font-family: '{self.font_family}';  /* Custom Font */
            }}

            QTabBar::tab:selected {{
                background: #4aba91;  /* Light Seafoam Green Selected Tab */
                color: #000000;  /* Black Text */
            }}

            /* Textboxes (Path Inputs) */
            QLineEdit#preset_folder_input,
            QLineEdit#output_folder_input,
            QLineEdit#rom_path_input,
            QLineEdit#retroarch_path_input,
            QLineEdit#core_path_input,
            QLineEdit#emotracker_path_input,
            QLineEdit#snes9x_path_input,
            QLineEdit#msu_folder_input {{
                border: 1px solid #4aba91;  /* Light Seafoam Green Border */
                border-radius: 4px;  /* Rounded Corners */
                padding: 5px;
                background-color: #ffffff;  /* White Background */
                color: #000000;  /* Black Text */
                font-family: '{self.font_family}';  /* Custom Font */
            }}

            QLineEdit#preset_folder_input:hover,
            QLineEdit#output_folder_input:hover,
            QLineEdit#rom_path_input:hover,
            QLineEdit#retroarch_path_input:hover,
            QLineEdit#core_path_input:hover,
            QLineEdit#emotracker_path_input:hover,
            QLineEdit#snes9x_path_input:hover,
            QLineEdit#msu_folder_input:hover {{
                border: 1px solid #d4ce46;  /* Golden Light on Hover */
            }}

            QLineEdit#preset_folder_input:focus,
            QLineEdit#output_folder_input:focus,
            QLineEdit#rom_path_input:focus,
            QLineEdit#retroarch_path_input:focus,
            QLineEdit#core_path_input:focus,
            QLineEdit#emotracker_path_input:focus,
            QLineEdit#snes9x_path_input:focus,
            QLineEdit#msu_folder_input:focus {{
                border: 1px solid #d4ce46;  /* Golden Light on Focus */
                background-color: #e0f7fa;  /* Light Background on Focus */
                color: #000000;  /* Black Text */
            }}
        """,
        "visualizer_colors": {
            "top": QtGui.QColor(74, 186, 145),    # Light Seafoam Green
            "bottom": QtGui.QColor(212, 206, 70)  # Golden Light
        }, "header_color": "#d4ce46"
    },
        }



        # Validate theme_name and set default to "Light" if not found
        if theme_name not in themes:
            print(f"Theme '{theme_name}' not found. Falling back to 'Dark' theme.")
            theme_name = "Dark"

        selected_theme = themes[theme_name]

                    # Set header color dynamically
        self.header_color = selected_theme["header_color"]

        try:
            self.setStyleSheet(selected_theme["stylesheet"])
            QtWidgets.QApplication.instance().setStyleSheet(selected_theme["stylesheet"])
        except Exception as e:
            print(f"Failed to apply theme '{theme_name}': {e}")

        # Update the visualizer's gradient colors
        if hasattr(self, 'audio_visualizer') and self.audio_visualizer:
            self.audio_visualizer.set_gradient_colors(
                selected_theme["visualizer_colors"]["top"],
                selected_theme["visualizer_colors"]["bottom"]
            )

        self.seed_update_timer.start(100)  # 100 ms delay


    def save_settings(self):
        """Save current settings to config.ini."""
        # Example implementation
        try:
            # Save current settings (e.g., volume, sensitivity) to config
            if "Settings" not in self.config:
                self.config.add_section("Settings")

            self.config["Settings"]["volume"] = str(int(self.volume_level * 100))
            self.config["Settings"]["sensitivity"] = str(self.audio_visualizer.sensitivity)

            with open(self.config_file, "w") as configfile:
                self.config.write(configfile)

            self.show_message("Settings saved successfully!")
        except Exception as e:
            self.show_message(f"Failed to save settings: {e}")


    def show_about_dialog(self):
        """Show an about dialog."""
        about_text = (
            "About This App\n\n"
            "This application is designed to assist users in generating and managing "
            "randomized seed data for The Legend of Zelda: A Link to the Past Randomizer (ALTTPR). "
            "The key functions include generating, launching and patching ALTTPR seeds, MSU handling and Preset use/customization \n\n"
            

            "I (@AllAboutBill) created this app as a helper for my every day rando play. Of course tools like Sahasrahbot and the ALTTPR website"
            " are already handy enough, I wanted to make something that was a one-stop-shop that could generate seeds, patch them,"
            " add MSU and launch in one click. This accomplishes that. \n\n"

            
            "This application draws significant inspiration and resources from both the pyz3r "
            "library and Sahasrahbot. These tools were invaluable in shaping the ideas, foundations and capabilities of this app.\n\n"
            
            "I know my code is very messy and probaly pretty buggy... but as a beginner to Python, this project has been an incredible learning experience."
            " I’ve been using ChatGPT to help me with things I dont understand, troubleshoot issues, and integrate new features \n\n\n\n"
            " If you have any issues or suggestions, you can DM on Twitch or Discord @AllAboutBill"
        )

        QtWidgets.QMessageBox.about(
            self,
            "About ALTTPR Seed Generator",
            about_text
        )





    def update_emulator_paths_visibility(self):
        """Show the appropriate emulator paths depending on the selected emulator."""
        if self.retroarch_radio.isChecked():
            # Show RetroArch paths, hide Snes9x path
            self.path_rows["retroarch_path"][0].setVisible(True)
            self.path_rows["retroarch_path"][1].setVisible(True)
            self.path_rows["retroarch_path"][2].setVisible(True)

            self.path_rows["core_path"][0].setVisible(True)
            self.path_rows["core_path"][1].setVisible(True)
            self.path_rows["core_path"][2].setVisible(True)

            self.path_rows["snes9x_path"][0].setVisible(False)
            self.path_rows["snes9x_path"][1].setVisible(False)
            self.path_rows["snes9x_path"][2].setVisible(False)

        elif self.snes9x_radio.isChecked():
            # Show Snes9x path, hide RetroArch paths
            self.path_rows["retroarch_path"][0].setVisible(False)
            self.path_rows["retroarch_path"][1].setVisible(False)
            self.path_rows["retroarch_path"][2].setVisible(False)

            self.path_rows["core_path"][0].setVisible(False)
            self.path_rows["core_path"][1].setVisible(False)
            self.path_rows["core_path"][2].setVisible(False)

            self.path_rows["snes9x_path"][0].setVisible(True)
            self.path_rows["snes9x_path"][1].setVisible(True)
            self.path_rows["snes9x_path"][2].setVisible(True)



    def create_paths_and_presets(self):
        """Create a combined section for paths and emulator selection."""
        self.paths_and_presets_groupbox = QtWidgets.QGroupBox("Paths and Folders")
        paths_and_presets_layout = QtWidgets.QVBoxLayout()

        # Add emulator selection buttons to the top of this section
        emulator_selection_layout = QtWidgets.QHBoxLayout()
        emulator_selection_layout.setContentsMargins(0, 0, 0, 0)  # Remove extra margins for compactness
        emulator_selection_layout.setSpacing(2)  # Reduce spacing between elements

        emulator_label = QtWidgets.QLabel("Select Emulator:  ")
        emulator_label.setSizePolicy(QtWidgets.QSizePolicy.Minimum, QtWidgets.QSizePolicy.Minimum)
        emulator_label.setStyleSheet("font-weight: bold;")

        # Styled RetroArch and Snes9x radio buttons
        self.retroarch_radio = QtWidgets.QRadioButton("RetroArch")
        self.snes9x_radio = QtWidgets.QRadioButton("Snes9x")
        self.retroarch_radio.setChecked(True)  # Set default to RetroArch

        # Assign unique objectNames to radio buttons for styling (optional)
        self.retroarch_radio.setObjectName("retroarchRadio")
        self.snes9x_radio.setObjectName("snes9xRadio")

        # Apply initial styles
        self.update_emulator_styles()

        # Create a separator label with minimized spacing for compact appearance
        separator_label = QtWidgets.QLabel("|")
        separator_label.setStyleSheet("padding: 0 5px; font-size: 14px; color: gray;")

        # Add radio buttons and separator to the layout, aligning to the right
        emulator_selection_layout.addStretch()  # Push buttons to the right
        emulator_selection_layout.addWidget(emulator_label)
        emulator_selection_layout.addWidget(self.retroarch_radio)
        emulator_selection_layout.addWidget(separator_label)
        emulator_selection_layout.addWidget(self.snes9x_radio)

        # Connect the toggled signals to update paths visibility and styles
        self.retroarch_radio.toggled.connect(self.update_emulator_paths_visibility)
        self.snes9x_radio.toggled.connect(self.update_emulator_paths_visibility)
        self.retroarch_radio.toggled.connect(self.update_emulator_styles)
        self.snes9x_radio.toggled.connect(self.update_emulator_styles)
        self.retroarch_radio.toggled.connect(self.save_emulator_preference)
        self.snes9x_radio.toggled.connect(self.save_emulator_preference)

        # Add emulator selection layout to the paths layout
        paths_and_presets_layout.addLayout(emulator_selection_layout)

        # Paths Configuration
        path_inputs_layout = QtWidgets.QFormLayout()

        # Define paths with labels
        labels_and_paths = [
            ("Preset Folder:", "preset_folder"),
            ("Output Folder:", "output_folder"),
            ("Base ROM Path:", "rom_path"),
            ("RetroArch Path:", "retroarch_path"),
            ("RetroArch Core Path:", "core_path"),
            ("EmoTracker Path:", "emotracker_path"),
            ("Snes9x Path:", "snes9x_path"),  # Added Snes9x path option
            ("MSU Pack Directory:", "msu_folder")  # Add MSU folder path option
        ]

        self.path_inputs = {}
        self.path_rows = {}

        for label_text, key in labels_and_paths:
            # Create the label
            label = QtWidgets.QLabel(label_text)

            # Input field
            input_field = QtWidgets.QLineEdit()
            input_field.setObjectName(f"{key}_input")  # Assign unique objectName based on key
            self.path_inputs[key] = input_field

            # Browse button
            browse_button = QtWidgets.QPushButton("Browse")
            browse_button.setObjectName(f"{key}_browse_button")  # Optional: Assign objectName for styling
            browse_button.clicked.connect(lambda _, k=key: self.browse_folder_or_file(k))

            # Create a horizontal layout for each row with input and button
            path_row_layout = QtWidgets.QHBoxLayout()
            path_row_layout.addWidget(input_field)
            path_row_layout.addWidget(browse_button)

            # Store references to each row (label, input field, browse button)
            self.path_rows[key] = (label, input_field, browse_button)

            # Add the label and the row layout to the form layout
            path_inputs_layout.addRow(label, path_row_layout)

        # Add the path inputs layout to the main paths and presets layout
        paths_and_presets_layout.addLayout(path_inputs_layout)

        # Set the combined layout for the group box
        self.paths_and_presets_groupbox.setLayout(paths_and_presets_layout)
        self.path_inputs["msu_folder"].textChanged.connect(self.save_config)

        # Add paths and presets to the main layout
        self.main_layout.addWidget(self.paths_and_presets_groupbox)

    def populate_msu_combobox(self):
        """Populate the MSU ComboBox with subfolder names from the MSU directory."""
        msu_directory = self.path_inputs["msu_folder"].text()  # Retrieve the MSU directory path

        if not os.path.exists(msu_directory):
            return None

        # Temporarily disconnect the MSU selection change signal to avoid triggering during refresh
        self.msu_combobox.blockSignals(True)

        # Clear existing items (but keep the 'Random' option)
        self.msu_combobox.clear()
        self.msu_combobox.addItem("Random")  # Always keep 'Random' as the first option

        # Find subfolders in the MSU directory
        subfolders = [f.name for f in os.scandir(msu_directory) if f.is_dir()]

        # Add each subfolder as an option in the ComboBox
        for subfolder in subfolders:
            self.msu_combobox.addItem(subfolder)

        # Optionally, you can select the first available MSU by default
        if subfolders:
            self.msu_combobox.setCurrentIndex(1)  # Select the first subfolder (after Random)

        # Reconnect the MSU selection change signal after refresh
        self.msu_combobox.blockSignals(False)




    def update_emulator_styles(self):
        """Update the styles of emulator buttons based on which one is selected."""
        if self.retroarch_radio.isChecked():
            self.retroarch_radio.setStyleSheet("""
                QRadioButton {
                    font-size: 11px;
                    padding: 2px 6px;
                    border-radius: 4px;
                    background-color: #007BFF;  /* Blue color for selected */
                    color: white;
                }
                QRadioButton::indicator {
                    width: 0px;  /* Hide default indicator for compact button look */
                    height: 0px;
                }
            """)
            self.snes9x_radio.setStyleSheet("""
                QRadioButton {
                    font-size: 11px;
                    padding: 2px 6px;
                    border-radius: 4px;
                    background-color: #333333;  /* Dark gray for unselected */
                    color: white;
                }
                QRadioButton::indicator {
                    width: 0px;  /* Hide default indicator for compact button look */
                    height: 0px;
                }
            """)
        elif self.snes9x_radio.isChecked():
            self.retroarch_radio.setStyleSheet("""
                QRadioButton {
                    font-size: 11px;
                    padding: 2px 6px;
                    border-radius: 4px;
                    background-color: #333333;  /* Dark gray for unselected */
                    color: white;
                }
                QRadioButton::indicator {
                    width: 0px;  /* Hide default indicator for compact button look */
                    height: 0px;
                }
            """)
            self.snes9x_radio.setStyleSheet("""
                QRadioButton {
                    font-size: 11px;
                    padding: 2px 6px;
                    border-radius: 4px;
                    background-color: #007BFF;  /* Blue color for selected */
                    color: white;
                }
                QRadioButton::indicator {
                    width: 0px;  /* Hide default indicator for compact button look */
                    height: 0px;
                }
        """)







    def toggle_paths_section(self):
        """Toggle the visibility of the paths and presets section."""
        if self.paths_and_presets_groupbox.isVisible():
            self.paths_and_presets_groupbox.setVisible(False)
            self.toggle_paths_button.setText("Show Paths")
        else:
            self.paths_and_presets_groupbox.setVisible(True)
            self.toggle_paths_button.setText("Hide Paths")


    def log_seed_history(self, preset_name, permalink):
        """Log the generated seed with preset, date, and permalink."""
        timestamp = datetime.now().strftime("%m-%d-%y %H:%M:%S")
        entry = f"Preset: {preset_name} | Date: {timestamp} | Permalink: {permalink}\n"
        with open("seed_history.txt", "a") as file:
            file.write(entry)



    def update_sprite_display_in_actions(self):
        """Update the QLabel in the actions box to display the selected sprite or animated GIF in a popup if available."""
        selected_sprite = self.patch_settings.get("spritename", "Link")

        # Replace spaces with '%20' in the selected sprite name to form a valid URL
        selected_sprite_encoded = selected_sprite.replace(" ", "%20")

        # Construct the URL for the sprite GIF
        gif_url = f"https://hyphen-ated.github.io/alttpr-sprite-gallery/spriteimgs/{selected_sprite_encoded}.gif"
        print(f"Trying GIF URL: {gif_url}")

        # Get the sprite index, handling "Random" as index 0
        sprite_index = 0 if selected_sprite == "Random" else self.get_sprite_index(selected_sprite)

        # Display the static sprite by default
        sprite_width, sprite_height = 16, 24  # Original sprite size
        scale_factor = 4
        scaled_width = sprite_width * scale_factor
        scaled_height = sprite_height * scale_factor

        if sprite_index is not None:
            # Extract and scale the sprite pixmap from the spritesheet using the same logic as in the dialog box
            sprite_pixmap = self.extract_and_scale_sprite(sprite_index, scale_factor)

            if not sprite_pixmap.isNull():
                # Set the scaled pixmap to the label
                self.sprite_display_label_in_actions.setFixedSize(scaled_width, scaled_height)

                # Create and set the SpriteLabel widget
                sprite_label = SpriteLabel(sprite_pixmap, gif_url, parent=self.sprite_display_label_in_actions)
                sprite_label.setFixedSize(scaled_width, scaled_height)
                sprite_label.show()

    def extract_and_scale_sprite(self, sprite_index, scale_factor):
        """Extract and scale the sprite from the spritesheet."""
        sprite_width, sprite_height = 16, 24  # Original sprite size
        x = (sprite_index % (self.spritesheet.width() // sprite_width)) * sprite_width
        y = (sprite_index // (self.spritesheet.width() // sprite_width)) * sprite_height

        sprite_pixmap = self.spritesheet.copy(x, y, sprite_width, sprite_height)

        if not sprite_pixmap.isNull():
            # Scale the pixmap using FastTransformation
            scaled_pixmap = sprite_pixmap.scaled(
                sprite_width * scale_factor,
                sprite_height * scale_factor,
                QtCore.Qt.KeepAspectRatio,
                QtCore.Qt.FastTransformation
            )
            return scaled_pixmap
        else:
            return QtGui.QPixmap()  # Return an empty pixmap if null

    def get_sprite_index(self, sprite_name):
        """Return the index of the sprite based on the sprite name."""
        for idx, sprite in enumerate(self.sprite_data):
            if sprite['name'] == sprite_name:
                return idx + 1  # Adding 1 to skip the "Random" sprite at index 0
        return None

    def create_permalink_input(self):
        """Create permalink input and add it to the main layout."""
        permalink_groupbox = QtWidgets.QGroupBox("Patch from Permalink")
        permalink_layout = QtWidgets.QHBoxLayout()

        # Permalink input, label, and button for patching
        self.permalink_label = QtWidgets.QLabel("Permalink:")
        self.permalink_field = QtWidgets.QLineEdit()
        self.permalink_field.setPlaceholderText("Enter permalink to seed")
        self.permalink_patch_button = QtWidgets.QPushButton("Patch")
        self.permalink_patch_button.clicked.connect(self.patch_from_permalink)

        # Connect the textChanged signal for automatic update
        self.permalink_field.textChanged.connect(self.on_permalink_changed)

        # Add elements to the permalink layout
        permalink_layout.addWidget(self.permalink_label)
        permalink_layout.addWidget(self.permalink_field)
        permalink_layout.addWidget(self.permalink_patch_button)

        permalink_groupbox.setLayout(permalink_layout)
        self.main_layout.addWidget(permalink_groupbox)


    def create_info_box(self):
        """Create an information box to display details about the seed."""
        info_groupbox = QtWidgets.QGroupBox("Seed Info")
        info_layout = QtWidgets.QVBoxLayout()

        # Create QLabel widgets for the info boxes
        self.info_box_left = QtWidgets.QLabel()
        self.info_box_right = QtWidgets.QLabel()

        # Apply theme-specific styles
        self.info_box_left.setStyleSheet(f"""
            QLabel {{
                font-size: 14px;
                background-color: transparent;
            }}
        """)
        self.info_box_right.setStyleSheet(f"""
            QLabel {{
                font-size: 14px;
                background-color: transparent;
            }}
        """)

        # Set word wrap for better formatting of content
        self.info_box_left.setWordWrap(True)
        self.info_box_right.setWordWrap(True)

        # Create a widget to combine both labels
        combined_widget = QtWidgets.QWidget()
        combined_layout = QtWidgets.QHBoxLayout(combined_widget)

        # Add both QLabels to the combined layout
        combined_layout.addWidget(self.info_box_left)
        combined_layout.addWidget(self.info_box_right)

        # Create a scroll area to contain the combined widget
        scroll_area = QtWidgets.QScrollArea()
        scroll_area.setWidgetResizable(True)
        scroll_area.setWidget(combined_widget)

        # Add the scroll area to the vertical layout
        info_layout.addWidget(scroll_area)

        info_groupbox.setLayout(info_layout)
        self.main_layout.addWidget(info_groupbox)




    def browse_folder_or_file(self, key):
        """Browse for folders or files depending on the input type."""
        # If the key corresponds to folder paths, we use folder selection
        if key in ["preset_folder", "output_folder", "msu_folder"]:  # Add "msu_folder" for folder selection
            folder = QFileDialog.getExistingDirectory(self, "Select Folder")
            if folder:
                self.path_inputs[key].setText(folder)
        else:
            # Define file types based on the key
            file_types = {
                "rom_path": "ROM Files (*.sfc);;All Files (*)",
                "retroarch_path": "Executable Files (*.exe);;All Files (*)",
                "core_path": "Core Files (*.dll);;All Files (*)",
                "emotracker_path": "Executable Files (*.exe);;All Files (*)",
                "snes9x_path": "Executable Files (*.exe);;All Files (*)"  # Added Snes9x path
            }

            # Use the key to get the appropriate file type, defaulting to "All Files (*)"
            file_type = file_types.get(key, "All Files (*)")
            file_path, _ = QFileDialog.getOpenFileName(self, "Select File", "", file_type)
            if file_path:
                self.path_inputs[key].setText(file_path)

        # Save the updated paths to the config file
        self.save_config()






    def on_permalink_changed(self):
        """Start a timer to delay fetching seed info when the permalink changes."""
        self.seed_update_timer.start(500)  # Delay of 500 milliseconds
        
    def on_update_seed_info_timeout(self):
        """Wrapper function to call the async update_and_display_seed_info."""
        self.seed_update_timer.stop()  # Stop the timer to prevent multiple executions

        try:
            # Try to get the current running loop
            loop = asyncio.get_running_loop()
        except RuntimeError:
            # If no running loop, create a new one
            loop = asyncio.new_event_loop()
            asyncio.set_event_loop(loop)

        if loop.is_running():
            # If the event loop is running, create a new task
            asyncio.create_task(self.update_and_display_seed_info())
        else:
            # If no loop is running, run the coroutine directly
            loop.run_until_complete(self.update_and_display_seed_info())

    async def update_and_display_seed_info(self):
        """Extract seed hash from permalink, fetch seed information, and update the display."""
        permalink = self.permalink_field.text().strip()
        match = re.search(r'alttpr.com/(?:[a-z]{2}/)?h/([A-Za-z0-9]+)', permalink)

        if not match:
            self.info_box_left.setText("Please input a valid permalink to view seed info.")
            self.info_box_right.setText("")
            return

        seed_hash = match.group(1)

        try:
            # Retrieve seed details using the hash
            alttpr = ALTTPR()
            daily_seed = await alttpr.retrieve(seed_hash)

            if not daily_seed or not daily_seed.data:
                # Clear both info boxes if no valid seed is found
                self.info_box_left.setText("")
                self.info_box_right.setText("")
                return

            # Extract and prepare the info text
            meta = daily_seed.data.get('spoiler', {}).get('meta', {})
            if not meta:
                # Clear both info boxes if no detailed settings are found
                self.info_box_left.setText("No detailed settings found for the seed.")
                self.info_box_right.setText("")
                return

            # Prepare logic section with conditional red highlight
            logic_value = meta.get('logic', 'N/A')
            logic_text = (
                f'<span style="color: red;">{logic_value}</span>'
                if logic_value.lower() != 'noglitches' else logic_value
            )

            # Prepare header style
            header_style = (
                "font-size: 18px;"
                "font-weight: bold;"
                "text-shadow: 1px 1px 4px #4a90e2, -1px -1px 4px #4a90e2, 1px -1px 4px #4a90e2, -1px 1px 4px #4a90e2;"
                f"color: {self.header_color};"
            )

            # Extract the "created" field and format it for display
            created_timestamp = daily_seed.data.get("generated", "N/A")
            if created_timestamp != "N/A":
                try:
                    created_date_utc = datetime.strptime(created_timestamp, "%Y-%m-%dT%H:%M:%S%z")
                    est_timezone = pytz.timezone("US/Eastern")
                    created_date_est = created_date_utc.astimezone(est_timezone)
                    created_date_formatted = created_date_est.strftime("%m/%d/%Y %I:%M %p")
                except ValueError:
                    created_date_formatted = created_timestamp
            else:
                created_date_formatted = "Creation date not available."

            # Prepare the general information text for the left column
            general_info_text = (
                f"<div style='{header_style}'>Seed Name:</div> {meta.get('name', 'N/A')}<br><br>"
                f"<b>Generated:</b> {created_date_formatted} EST<br><br>"
                f"<div style='{header_style}'>=== Game Settings ===</div><br>"
                f"<b>Mode:</b> {meta.get('mode', 'N/A')}<br>"
                f"<b>Weapons:</b> {meta.get('weapons', 'N/A')}<br>"
                f"<b>Goal:</b> {meta.get('goal', 'N/A')}<br>"
                f"<b>Logic:</b> {logic_text}<br>"
                f"<b>Dungeon Items:</b> {meta.get('dungeon_items', 'N/A')}<br>"
                f"<b>Item Placement:</b> {meta.get('item_placement', 'N/A')}<br>"
                f"<b>Item Pool:</b> {meta.get('item_pool', 'N/A')}<br>"
                f"<b>Item Functionality:</b> {meta.get('item_functionality', 'N/A')}<br><br>"
                f"<div style='{header_style}'>=== Requirements ===</div><br>"
                f"<b>Crystals to Defeat Ganon:</b> {meta.get('entry_crystals_ganon', 'N/A')}<br>"
                f"<b>Crystals to Enter Tower:</b> {meta.get('entry_crystals_tower', 'N/A')}<br><br>"
            )

            # Extract and display the file select code with images
            file_select_info_text = ""
            try:
                file_select_code = daily_seed.code
                item_to_filename = {
                    "Flute": "ocarinainactive",
                    "Bugnet": "bugcatchingnet",
                    "Magic Powder": "powder",
                    "Ice Rod": "icerod",
                    "Fire Rod": "firerod",
                    "Cape": "cape",
                    "Boots": "pegasusboots",
                    "Moon Pearl": "Moonpearl",
                    "Mirror": "MagicMirror",
                    "Gloves": "glove",
                    "Book": "BookofMudora",
                    "Heart": "BossHeartContainer",
                    "Empty Bottle": "Bottle",
                    "Somaria": "CaneOfSomaria",
                    "Byrna": "CaneOfByrna",
                    "Tunic": "GreenMail",
                    "Shield": "Mirror Shield"
                }

                if file_select_code:
                    icons_text = ""
                    for item in file_select_code:
                        filename = item_to_filename.get(item, item).lower()
                        icon_path = resource_path(f"images/{filename}.png")
                        if os.path.exists(icon_path):
                            icons_text += f'<img src="{icon_path}" width="24" height="24" /> '
                        else:
                            icons_text += f"{item} "

                    file_select_info_text = (
                        f"<div style='{header_style}'>=== File Select Code ===</div><br>{icons_text}<br><br>"
                    )
                else:
                    file_select_info_text = f"<div style='{header_style}'>=== File Select Code ===</div><br>N/A<br><br>"
            except Exception as e:
                file_select_info_text = f"<div style='{header_style}'>=== File Select Code ===</div><br>An error occurred: {e}<br><br>"

            # Prepare the Enemizer and Miscellaneous sections for the right column
            additional_details_text = (
                file_select_info_text +
                f"<div style='{header_style}'>=== Enemizer Settings ===</div><br>"
                f"<b>Boss Shuffle:</b> {meta.get('enemizer.boss_shuffle', 'N/A')}<br>"
                f"<b>Enemy Shuffle:</b> {meta.get('enemizer.enemy_shuffle', 'N/A')}<br>"
                f"<b>Enemy Damage:</b> {meta.get('enemizer.enemy_damage', 'N/A')}<br>"
                f"<b>Enemy Health:</b> {meta.get('enemizer.enemy_health', 'N/A')}<br>"
                f"<b>Pot Shuffle:</b> {meta.get('enemizer.pot_shuffle', 'N/A')}<br><br>"
                f"<div style='{header_style}'>=== Miscellaneous ===</div><br>"
                f"<b>Hints:</b> {meta.get('hints', 'N/A')}<br>"
                f"<b>Spoilers:</b> {meta.get('spoilers', 'N/A')}<br>"
                f"<b>Allow Quickswap:</b> {meta.get('allow_quickswap', 'N/A')}<br>"
                f"<b>Pseudoboots:</b> {meta.get('pseudoboots', 'N/A')}<br>"
                f"<b>Tournament:</b> {'Yes' if meta.get('tournament', False) else 'No'}<br>"
            )

            # Display the information in the info boxes
            self.info_box_left.setText(general_info_text)
            self.info_box_right.setText(additional_details_text)

            # Display the seed URL in the permalink field
            if hasattr(daily_seed, 'url'):
                self.permalink_field.setText(daily_seed.url)

        except Exception as e:
            self.info_box_left.setText("")  # Clear left box in case of error
            self.info_box_right.setText("")  # Clear right box







    def patch_from_permalink(self):
        """Handle patching from permalink by extracting the seed hash and initiating the patching process."""
        permalink = self.permalink_field.text().strip()
        if not permalink:
            QtWidgets.QMessageBox.warning(self, "Input Error", "Please enter a valid permalink.")
            return

        # Validate and extract the seed hash from the permalink
        match = re.search(r'alttpr.com/(?:[a-z]{2}/)?h/([A-Za-z0-9]+)', permalink)
        if match:
            seed_hash = match.group(1)
            asyncio.create_task(self.patch_and_launch_rom(seed_hash))
        else:
            QtWidgets.QMessageBox.warning(self, "Input Error", "Please enter a valid permalink URL.")
    
    def generate_patch_settings(self):
        """Generate patch settings based on the current selections in self.patch_settings."""
        patch_settings = {
            "heartspeed": self.patch_settings.get("heartspeed", "normal"),
            "heartcolor": self.patch_settings.get("heartcolor", "red"),
            "spritename": self.patch_settings.get("spritename", "Old Man"),
            "music": self.patch_settings.get("music", True),
            "quickswap": self.patch_settings.get("quickswap", True),
            "menu_speed": self.patch_settings.get("menu_speed", "normal"),
            "msu1_resume": self.patch_settings.get("msu1_resume", True)
        }

        # Retrieve MSU folder path safely
        msu_folder = self.path_inputs.get("msu_folder", "").text()

        # Debugging output to check current settings
        print(f"[DEBUG] Patch settings before random color handling: {patch_settings}")

        # If heart color is set to "random", pick a valid color
        if patch_settings["heartcolor"] == "random":
            print("[DEBUG] Heart color is random, choosing a new color.")
            patch_settings["heartcolor"] = random.choice(['red', 'blue', 'green', 'yellow'])

        # Assign the MSU folder path to patch_settings if applicable
        patch_settings["msu_path"] = msu_folder

        return patch_settings



    def launch_retroarch_with_rom(self, rom_path):
        """Launch RetroArch with the specified ROM, handling MSU support if applicable."""
        # Terminate any existing RetroArch process
        self.terminate_existing_process("retroarch.exe")

        # Extract the folder and base name of the ROM
        rom_folder = os.path.dirname(rom_path)
        rom_base = os.path.basename(rom_path)  # Get the full ROM file name with extension

        # If MSU is used, ensure the ROM is in the correct subfolder
        if self.use_msu_checkbox.isChecked():
            rom_base_name = os.path.splitext(rom_base)[0]  # Get the ROM base name without extension
            rom_folder_with_msu = os.path.join(rom_folder, rom_base_name)
            
            # If the MSU folder exists, adjust the rom_folder and rom_base path
            if os.path.isdir(rom_folder_with_msu):
                rom_folder = rom_folder_with_msu
                rom_base = f"{rom_base_name}.sfc"  # Ensure the .sfc extension

        retroarch_path = self.path_inputs["retroarch_path"].text()  # RetroArch executable path
        core_path = self.path_inputs["core_path"].text()  # RetroArch core path

        # Check if RetroArch and the core paths are valid
        if not os.path.exists(retroarch_path) or not os.path.exists(core_path):
            self.show_message("RetroArch or core path not found. Please check the paths.")
            return

        # Construct the command: cd into the correct folder, and run RetroArch with the full ROM path
        command = f'cd "{rom_folder}" && "{retroarch_path}" -L "{core_path}" "{rom_base}"'

        # Print the command for debugging
        print(f"Launching RetroArch with command: {command}")

        # Execute the command
        subprocess.Popen(command, shell=True)


    async def patch_and_launch_rom(self, seed_hash):
        """Patch the ALTTPR seed and optionally launch the selected emulator or EmoTracker."""
        input_rom_path = self.path_inputs['rom_path'].text()
        if not os.path.exists(input_rom_path):
            self.show_message("Base ROM not found. Please ensure it exists.")
            return

        output_rom_folder = self.path_inputs['output_folder'].text()  # Base folder where ROMs should be saved
        output_rom_path = os.path.join(output_rom_folder, f"{seed_hash}.sfc")
        msu_folder = self.path_inputs.get("msu_folder")  # Get the MSU folder path

        if msu_folder:
            msu_folder = msu_folder.text()  # Extract text only if msu_folder exists

        try:
            # Retrieve the seed
            seed = await ALTTPR.retrieve(hash_id=seed_hash)

            # Generate patch settings with any needed adjustments (e.g., replacing "random" for heart color)
            patch_settings = self.generate_patch_settings()

            # Patch the ROM with user settings (without passing msu_path directly)
            await seed.create_patched_game(
                input_filename=input_rom_path,
                output_filename=output_rom_path,
                heartspeed=patch_settings["heartspeed"],
                heartcolor=patch_settings["heartcolor"],
                spritename=patch_settings["spritename"],
                music=patch_settings["music"],
                quickswap=patch_settings["quickswap"],
                menu_speed=patch_settings["menu_speed"]
            )
            self.show_message(f"Patched ROM saved to: {output_rom_path}")

            rom_final_path = output_rom_path  # Default to the original ROM path
            
            # Handle MSU setup only if the "Use MSU Soundtrack" checkbox is checked
            if self.use_msu_checkbox.isChecked() and msu_folder and os.path.isdir(msu_folder):
                msu_result = self.setup_msu_files(msu_folder, output_rom_path)  # Adjust ROM path based on MSU
                if msu_result:  # Check if MSU setup succeeded
                    rom_final_path = msu_result
                    
            # Determine whether to launch an emulator and which one
            if self.launch_emulator_checkbox.isChecked():
                if self.retroarch_radio.isChecked():
                    print(f"Launching RetroArch with ROM path: {rom_final_path}")  # Debugging statement
                    self.launch_retroarch_with_rom(rom_final_path)
                elif self.snes9x_radio.isChecked():
                    print(f"Launching Snes9x with ROM path: {rom_final_path}")  # Debugging statement
                    self.launch_snes9x_with_rom(rom_final_path)
                else:
                    print("No emulator selected.")

            # Launch EmoTracker if checkbox is checked
            if self.launch_emotracker_checkbox.isChecked():
                self.launch_emotracker()
                        
        except Exception as e:
            self.show_message(f"Error while patching ROM: {e}")
            print(f"[DEBUG] Error while patching ROM: {e}")




    def setup_msu_files(self, msu_base_folder, rom_path):
        """Ensure MSU files are placed in the correct folder and named properly, skipping missing PCM files."""
        # Get the selected MSU pack from the combo box
        selected_msu_pack = self.msu_combobox.currentText()

        # If "Random" is selected, randomly pick an MSU pack
        if selected_msu_pack == "Random":
            # Check if there are any MSU packs available in the folder
            msu_packs = [f.name for f in os.scandir(msu_base_folder) if f.is_dir()]
            if not msu_packs:
                self.show_message("No MSU packs found in the MSU folder.")
                return False

            # Randomly choose an MSU pack from the available options
            selected_msu_pack = random.choice(msu_packs)
            print(f"Random MSU selected. The chosen pack is: {selected_msu_pack}")

        # The MSU pack folder path
        msu_folder = os.path.join(msu_base_folder, selected_msu_pack)

        if not os.path.exists(msu_folder):
            self.show_message(f"Selected MSU pack folder {msu_folder} does not exist.")
            return False

        # Get the directory and base name of the ROM, excluding the extension
        rom_folder = os.path.dirname(rom_path)
        rom_base = os.path.splitext(os.path.basename(rom_path))[0]  # Base name without extension

        # Create the MSU folder if it doesn't already exist
        msu_output_folder = os.path.join(rom_folder, rom_base)
        if not os.path.exists(msu_output_folder):
            os.makedirs(msu_output_folder)

        # Move the ROM to the MSU folder if it isn't already there
        rom_new_path = os.path.join(msu_output_folder, f"{rom_base}.sfc")
        if rom_path != rom_new_path and not os.path.exists(rom_new_path):
            try:
                shutil.move(rom_path, rom_new_path)
            except Exception as e:
                self.show_message(f"Failed to move ROM to MSU folder: {e}")
                return False

        # Handle MSU files
        msu_files = [f for f in os.listdir(msu_folder) if f.endswith(".msu")]
        if not msu_files:
            # If no MSU file exists, create a dummy .msu file
            msu_file = os.path.join(msu_output_folder, f"{rom_base}.msu")
            try:
                open(msu_file, 'w').close()  # Create an empty .msu file
                print(f"Created dummy MSU file: {msu_file}")
            except Exception as e:
                self.show_message(f"Failed to create MSU file: {e}")
                return False
        else:
            msu_src_file = os.path.join(msu_folder, msu_files[0])
            msu_file = os.path.join(msu_output_folder, f"{rom_base}.msu")
            if not os.path.exists(msu_file):
                try:
                    shutil.copy(msu_src_file, msu_file)
                    print(f"Copied MSU file from {msu_src_file} to {msu_file}")
                except Exception as e:
                    self.show_message(f"Failed to copy MSU file: {e}")
                    return False

        # Copy PCM files to the folder and rename them based on their original numbering, skipping missing files
        pcm_files = [f for f in os.listdir(msu_folder) if f.endswith('.pcm')]
        print(f"Total PCM files found: {len(pcm_files)}")
        print(pcm_files)  # Print out the list of PCM files for debugging

        # Use a sorted version of pcm_files to ensure files are processed in order
        sorted_pcm_files = sorted(pcm_files, key=lambda f: int(re.search(r'-(\d+)\.pcm$', f).group(1)) if re.search(r'-(\d+)\.pcm$', f) else float('inf'))

        for pcm_file in sorted_pcm_files:
            try:
                # Extract track number from the PCM file
                track_match = re.search(r'-(\d+)\.pcm$', pcm_file)
                if track_match:
                    track_number = int(track_match.group(1))
                else:
                    print(f"Track number not found in {pcm_file}. Skipping this file.")
                    continue

                # Create source and destination file paths
                src_pcm_file = os.path.join(msu_folder, pcm_file)
                dst_pcm_file = os.path.join(msu_output_folder, f"{rom_base}-{track_number}.pcm")

                # Check if the PCM file exists before copying
                if os.path.exists(src_pcm_file):
                    shutil.copy(src_pcm_file, dst_pcm_file)
                    print(f"Copied PCM file from {src_pcm_file} to {dst_pcm_file}")
                else:
                    print(f"Track {track_number} missing, skipping this track.")
            except IndexError as e:
                print(f"IndexError occurred at track {track_number}: {e}. This might be an issue with the MSU pack file structure.")
                return False
            except Exception as e:
                self.show_message(f"Failed to process PCM file for track {pcm_file}: {e}")
                return False

        # Return the path of the folder where the ROM and MSU files are located
        return msu_output_folder











    async def fetch_daily_seed_async(self):
        """Asynchronous function to fetch the daily seed."""
        try:
            async with aiohttp.ClientSession() as session:
                response = await session.get("https://alttpr.com/api/daily")
                data = await response.json()

                # Assuming the response contains the seed hash
                seed_hash = data.get('hash', '')
                if seed_hash:
                    # Construct the permalink and update the permalink field
                    permalink = f"https://alttpr.com/h/{seed_hash}"
                    self.permalink_field.setText(permalink)

                    # Use the combined method to fetch and display additional seed information
                    await self.update_and_display_seed_info()
                else:
                    self.info_box_left.setText("Failed to fetch daily seed: No hash available.")
                    self.info_box_right.setText("")
        except Exception as e:
            self.info_box_left.setText(f"An error occurred while fetching the daily seed: {e}")
            self.info_box_right.setText("")

    def launch_snes9x_with_rom(self, rom_path):
        """Launch Snes9x with the specified ROM and MSU support."""
        # Terminate existing Snes9x instances
        self.terminate_existing_process("snes9x.exe")

        try:
            snes9x_path = self.path_inputs["snes9x_path"].text().replace("\\", "/")  # Snes9x Path (forward slashes)

            # Check if Snes9x path exists
            if not os.path.exists(snes9x_path):
                self.show_message(f"Snes9x executable not found at {snes9x_path}. Please check the path.")
                return

            # Convert rom_path to forward slashes
            rom_final_path = rom_path.replace("\\", "/")

            # Handle MSU setup if MSU option is checked
            if self.use_msu_checkbox.isChecked():
                msu_folder = self.path_inputs.get("msu_folder", None)
                if msu_folder is not None and os.path.isdir(msu_folder.text()):
                    # Move ROM and MSU files to the correct MSU folder and get the updated ROM path
                    rom_final_path = self.setup_msu_files(msu_folder.text(), rom_final_path).replace("\\", "/")

            # Ensure the ROM file is correctly named and placed in the folder
            rom_folder = os.path.dirname(rom_final_path)
            rom_base = os.path.splitext(os.path.basename(rom_final_path))[0]  # Base ROM name
            rom_subfolder = os.path.join(rom_folder, rom_base)

            # If MSU is enabled and the subfolder exists, use the ROM from the subfolder
            if os.path.isdir(rom_subfolder):
                rom_final_path = os.path.join(rom_subfolder, f"{rom_base}.sfc").replace("\\", "/")

            # Ensure the ROM path includes the .sfc extension
            if not rom_final_path.endswith(".sfc"):
                rom_final_path += ".sfc"

            # Construct the command to launch Snes9x
            command = f'"{snes9x_path}" "{rom_final_path}"'

            # Print the final command for debugging
            print(f"Command to launch Snes9x: {command}")

            # Execute the command
            subprocess.Popen(shlex.split(command))

        except Exception as e:
            self.show_message(f"Failed to launch Snes9x: {e}")








    def fetch_daily_seed(self):
        """Fetch the daily seed by creating an asyncio task."""
        asyncio.create_task(self.fetch_daily_seed_async())



    def create_preset_selection(self):
        """Create the preset selection dropdown and refresh button."""
        preset_selection_layout = QtWidgets.QHBoxLayout()
        self.preset_label = QtWidgets.QLabel("Select Preset:")
        self.preset_dropdown = QtWidgets.QComboBox()
        self.refresh_presets_button = QtWidgets.QPushButton("Refresh Presets")
        self.refresh_presets_button.clicked.connect(self.load_presets)

        # Create the advanced preset button (moved here)
        self.advanced_seed_button = QtWidgets.QPushButton("Create Custom Preset")
        self.advanced_seed_button.clicked.connect(self.create_advanced_preset)

        # Add widgets to the preset selection layout
        preset_selection_layout.addWidget(self.preset_label)
        preset_selection_layout.addWidget(self.preset_dropdown)
        preset_selection_layout.addWidget(self.refresh_presets_button)
        preset_selection_layout.addWidget(self.advanced_seed_button)  # Add the Create Custom Preset button here

        return preset_selection_layout



    def load_config(self):
        """Load configuration from the config.ini file if it exists."""
        if os.path.exists(self.config_file):
            self.config.read(self.config_file)

            # Load Paths
            if "Paths" in self.config:
                paths = self.config["Paths"]
                keys = ["preset_folder", "output_folder", "rom_path", "retroarch_path", "core_path", "emotracker_path", "snes9x_path", "msu_folder"]
                for key in keys:
                    if key in paths and key in self.path_inputs:
                        self.path_inputs[key].setText(paths.get(key, ""))

            # Load checkboxes
            if "Checkboxes" in self.config:
                checkboxes = self.config["Checkboxes"]
                # Set checkbox states (convert from string to boolean)
                self.patch_checkbox.setChecked(checkboxes.get("patch_rom", "False") == "True")
                self.launch_emulator_checkbox.setChecked(checkboxes.get("launch_emulator", "False") == "True")
                self.launch_emotracker_checkbox.setChecked(checkboxes.get("launch_emotracker", "False") == "True")
                self.use_msu_checkbox.setChecked(checkboxes.get("use_msu", "False") == "True")

            # Load Patch Settings
            if "PatchSettings" in self.config:
                patch_settings = self.config["PatchSettings"]
                self.patch_settings["heartspeed"] = patch_settings.get("heartspeed", "normal")
                self.patch_settings["heartcolor"] = patch_settings.get("heartcolor", "red")
                self.patch_settings["spritename"] = patch_settings.get("spritename", "Old Man")
                self.patch_settings["menu_speed"] = patch_settings.get("menu_speed", "normal")
                self.patch_settings["music"] = patch_settings.getboolean("music", True)
                self.patch_settings["quickswap"] = patch_settings.getboolean("quickswap", True)
                self.patch_settings["msu1_resume"] = patch_settings.getboolean("msu1_resume", True)

                # Update UI elements based on `self.patch_settings`
                self.update_patch_settings_ui()

            # Load Emulator Preference and set the appropriate radio button
            if "Emulator" in self.config:
                emulator = self.config["Emulator"].get("selected_emulator", "retroarch")
                if emulator == "retroarch":
                    self.retroarch_radio.setChecked(True)
                elif emulator == "snes9x":
                    self.snes9x_radio.setChecked(True)

            # Load theme
            theme = self.config.get("Settings", "theme", fallback="Nightshade")
            self.apply_theme(theme)

            # Update paths visibility based on selected emulator
            self.update_emulator_paths_visibility()

            print("[DEBUG] Configuration loaded successfully.")
        else:
            print("[DEBUG] Configuration file not found. Using default settings.")





    def save_config(self):
        """Save current paths, checkbox states, and other settings to the config.ini file."""
        # Do not save during initial config loading
        if self.loading_config:
            return

        # Save Paths
        self.config["Paths"] = {
            "preset_folder": self.path_inputs["preset_folder"].text(),
            "output_folder": self.path_inputs["output_folder"].text(),
            "rom_path": self.path_inputs["rom_path"].text(),
            "retroarch_path": self.path_inputs["retroarch_path"].text(),
            "core_path": self.path_inputs["core_path"].text(),
            "emotracker_path": self.path_inputs["emotracker_path"].text(),
            "snes9x_path": self.path_inputs["snes9x_path"].text(),
            "msu_folder": self.path_inputs["msu_folder"].text()
        }

        # Save Patch Settings
        self.config["PatchSettings"] = {
            'heartspeed': self.patch_settings["heartspeed"],
            'heartcolor': self.patch_settings["heartcolor"],
            'spritename': self.patch_settings["spritename"],
            'menu_speed': self.patch_settings["menu_speed"],
            'music': str(self.patch_settings["music"]),
            'quickswap': str(self.patch_settings["quickswap"]),
            'msu1_resume': str(self.patch_settings["msu1_resume"])
        }

        # Save checkbox states
        self.config["Checkboxes"] = {
            "patch_rom": str(self.patch_checkbox.isChecked()),
            "launch_emulator": str(self.launch_emulator_checkbox.isChecked()),
            "launch_emotracker": str(self.launch_emotracker_checkbox.isChecked()),
            "use_msu": str(self.use_msu_checkbox.isChecked())
        }

        # Save Emulator Preference
        selected_emulator = "retroarch" if self.retroarch_radio.isChecked() else "snes9x"
        self.config["Emulator"] = {
            "selected_emulator": selected_emulator
        }

        # Save the audio volume level
        if "Audio" not in self.config:
            self.config.add_section("Audio")
        self.config["Audio"]["volume"] = str(self.volume_slider.value())

        # Save the selected theme
        if hasattr(self, 'current_theme'):
            if "Settings" not in self.config:
                self.config.add_section("Settings")
            self.config["Settings"]["theme"] = self.current_theme

        # Debugging: Print the current configuration before writing
        print("[DEBUG] Saving configuration:")
        for section in self.config.sections():
            print(f"[{section}]")
            for key, value in self.config[section].items():
                print(f"{key} = {value}")

        # Write the updated config to the file
        try:
            with open(self.config_file, "w") as configfile:
                self.config.write(configfile)
            print("[DEBUG] Configuration saved successfully.")
        except Exception as e:
            print(f"[ERROR] Failed to save configuration: {e}")
            self.show_message(f"Failed to save settings: {e}")
    
    def update_patch_settings_ui(self):
        """Update UI elements to reflect the current patch settings."""
        # Example for heart speed dropdown
        # Assuming you have a QComboBox for heart speed named `heart_speed_combo`
        if hasattr(self, 'heart_speed_combo'):
            index = self.heart_speed_combo.findText(self.patch_settings["heartspeed"], QtCore.Qt.MatchFixedString)
            if index >= 0:
                self.heart_speed_combo.setCurrentIndex(index)

        # Example for heart color
        # Assuming you have a QComboBox for heart color named `heart_color_combo`
        if hasattr(self, 'heart_color_combo'):
            index = self.heart_color_combo.findText(self.patch_settings["heartcolor"], QtCore.Qt.MatchFixedString)
            if index >= 0:
                self.heart_color_combo.setCurrentIndex(index)

        # Example for sprite name
        # Assuming you have a QComboBox for sprite name named `sprite_name_combo`
        if hasattr(self, 'sprite_name_combo'):
            index = self.sprite_name_combo.findText(self.patch_settings["spritename"], QtCore.Qt.MatchFixedString)
            if index >= 0:
                self.sprite_name_combo.setCurrentIndex(index)

        # Example for music checkbox
        if hasattr(self, 'music_checkbox'):
            self.music_checkbox.setChecked(self.patch_settings["music"])

        # Example for quickswap checkbox
        if hasattr(self, 'quickswap_checkbox'):
            self.quickswap_checkbox.setChecked(self.patch_settings["quickswap"])

        # Example for menu speed dropdown
        if hasattr(self, 'menu_speed_combo'):
            index = self.menu_speed_combo.findText(self.patch_settings["menu_speed"], QtCore.Qt.MatchFixedString)
            if index >= 0:
                self.menu_speed_combo.setCurrentIndex(index)

        # Example for MSU1 Resume checkbox
        if hasattr(self, 'msu1_resume_checkbox'):
            self.msu1_resume_checkbox.setChecked(self.patch_settings["msu1_resume"])

        # Update other UI elements as necessary
        # ...

        print("[DEBUG] UI elements updated based on patch settings.")


    def open_customize_patch_dialog(self):
        """Open the Customize Patch dialog and update sprite image if changed."""
        dialog = CustomizePatchDialog(self.patch_settings, self)
        if dialog.exec_():
            # Update patch settings after closing the dialog
            self.patch_settings = dialog.get_patch_settings()
            # Update sprite display in actions box
            self.update_sprite_display_in_actions()
            self.save_config()

    def create_advanced_preset(self):
        """Create a custom preset with advanced settings."""
        preset_folder = self.path_inputs["preset_folder"].text()  # Access the preset folder path using the correct key
        dialog = AdvancedCustomizeSeedDialog(preset_folder, self)

        if dialog.exec_():
            custom_settings = dialog.get_custom_settings()
            preset_name = dialog.get_preset_name()

            if preset_name:
                # Save the custom settings to a JSON file
                preset_path = os.path.join(preset_folder, f"{preset_name}.json")
                dialog.save_custom_settings_to_json(preset_path)

                # Update the preset list for customizer or randomizer as applicable
                if custom_settings.get("customizer", False):
                    self.customizer_presets.append(preset_name)
                else:
                    self.randomizer_presets.append(preset_name)

                # Reload presets to include the new advanced preset
                self.load_presets()




    def load_presets(self):
        """Load preset names from the preset folder and display them in the dropdown."""
        # Get the path from the input field using the dictionary key
        preset_folder = self.path_inputs["preset_folder"].text()

        # If the preset folder path exists, load presets from it
        if os.path.isdir(preset_folder):
            presets = self.load_presets_from_folder(preset_folder)
            self.preset_dropdown.clear()
            self.preset_dropdown.addItems(presets)
        else:
            QtWidgets.QMessageBox.warning(self, "Invalid Path", "Please provide a valid Preset Folder path.")

    def load_presets_from_folder(self, folder_path):
        """Helper method to get a list of preset names from the folder."""
        presets = []
        if os.path.isdir(folder_path):
            # Find all .json and .yaml/.yml files in the folder
            for filename in os.listdir(folder_path):
                if filename.endswith(".json") or filename.endswith(".yaml") or filename.endswith(".yml"):
                    # Add the file name without the extension
                    presets.append(os.path.splitext(filename)[0])
        return presets



    def generate_seed(self):
        """Generate the seed based on the selected preset and options."""
        preset_name = self.preset_dropdown.currentText()
        preset_folder = self.path_inputs['preset_folder'].text()

        if not preset_name:
            self.show_message("Please select a preset.")
            return

        # Determine the file path for the selected preset (either JSON or YAML)
        json_file_path = os.path.join(preset_folder, f"{preset_name}.json")
        yaml_file_path = os.path.join(preset_folder, f"{preset_name}.yaml")

        # Determine if the preset file exists, and whether it's JSON or YAML
        if os.path.exists(json_file_path):
            file_path = json_file_path
            file_type = "json"
        elif os.path.exists(yaml_file_path):
            file_path = yaml_file_path
            file_type = "yaml"
        else:
            self.show_message(f"Preset '{preset_name}' is not available.")
            return

        # Load the preset based on the file type
        try:
            if file_type == "json":
                with open(file_path, "r") as file:
                    payload = json.load(file)
            elif file_type == "yaml":
                with open(file_path, "r") as file:
                    payload = yaml.safe_load(file)
        except Exception as e:
            self.show_message(f"Failed to load the preset '{preset_name}'.")
            print(f"Error loading {file_type.upper()} file '{file_path}': {e}")
            return

        # Detect if JSON file matches the ALTTPR website format and convert it
        if file_type == "json" and "randomizer.glitches_required" in payload:
            payload = self.convert_alttpr_json_to_custom(payload)

        # Determine the correct API based on the presence of 'entrances' in the payload
        if 'entrances' in payload:
            # Use the Randomizer API
            api_url = self.randomizer_url
            self.api_type = "Randomizer"
        else:
            # Use the Customizer API
            api_url = self.customizer_url
            self.api_type = "Customizer"
            self.ensure_item_counts(payload)

        # Ensure the payload values are valid
        self.ensure_valid_payload(payload)

        # Use asyncio.create_task to call the asynchronous function within the event loop
        asyncio.create_task(self.generate_seed_with_api(payload, preset_name, api_url, self.api_type))


    def convert_alttpr_json_to_custom(self, json_data):
        """Convert the ALTTPR JSON format to a format compatible with generate_seed_with_api."""
        custom_settings = {
            "glitches": json_data.get("randomizer.glitches_required", "none"),
            "item_placement": json_data.get("randomizer.item_placement", "advanced"),
            "dungeon_items": json_data.get("randomizer.dungeon_items", "full"),
            "accessibility": json_data.get("randomizer.accessibility", "items"),
            "goal": json_data.get("randomizer.goal", "ganon"),
            "crystals": {
                "ganon": json_data.get("randomizer.ganon_open", "7"),
                "tower": json_data.get("randomizer.tower_open", "7")
            },
            "mode": json_data.get("randomizer.world_state", "open"),
            "hints": json_data.get("randomizer.hints", "on"),
            "weapons": json_data.get("randomizer.weapons", "assured"),
            "item": {
                "pool": json_data.get("randomizer.item_pool", "normal"),
                "functionality": json_data.get("randomizer.item_functionality", "normal")
            },
            "tournament": False,  # Assuming default value, since it's not in provided JSON
            "spoilers": "on",  # Assuming default value, since it's not in provided JSON
            "lang": "en",  # Assuming default value, since it's not in provided JSON
            "enemizer": {
                "boss_shuffle": json_data.get("randomizer.boss_shuffle", "none"),
                "enemy_shuffle": json_data.get("randomizer.enemy_shuffle", "none"),
                "enemy_damage": json_data.get("randomizer.enemy_damage", "default"),
                "enemy_health": json_data.get("randomizer.enemy_health", "default")
            },
            "name": json_data.get("vt.custom.name", ""),
            "notes": json_data.get("vt.custom.notes", ""),
            "l": {},
            "eq": [],  # To store starting items
            "drops": {},  # Assuming no drops specified
            "custom": json_data.get("vt.custom.settings", {}),
        }

        # Mapping for bottle types
        bottle_mapping = {
            1: "Bottle",
            2: "BottleWithGreenPotion",
            3: "BottleWithRedPotion",
            4: "BottleWithGoldBee",
            5: "BottleWithBluePotion",
            6: "BottleWithBee",
            7: "BottleWithFairy"
        }

        # Process bottles and add them to the 'eq' list
        bottle_keys = ["Bottle1", "Bottle2", "Bottle3", "Bottle4"]
        for bottle_key in bottle_keys:
            bottle_value = json_data.get("vt.custom.equipment", {}).get(bottle_key, None)
            if bottle_value is not None and bottle_value in bottle_mapping:
                bottle_name = bottle_mapping[bottle_value]
                custom_settings["eq"].append(bottle_name)

        # Add other starting equipment to the 'eq' list
        equipment = json_data.get("vt.custom.equipment", {})

        # Process Progressive Bow and convert to Bow or BowAndSilverArrows
        progressive_bow_value = equipment.get("ProgressiveBow", 0)
        if progressive_bow_value == 1:
            custom_settings["eq"].append("Bow")
        elif progressive_bow_value >= 2:
            custom_settings["eq"].append("BowAndSilverArrows")

        # Add other items excluding bottles and bow, which have already been processed
        for item, value in equipment.items():
            if item.startswith("Bottle") or item == "ProgressiveBow":
                continue
            if isinstance(value, bool) and value:
                custom_settings["eq"].append(item)
            elif isinstance(value, int) and value > 0:
                custom_settings["eq"].extend([item] * value)

        return custom_settings




    def ensure_valid_payload(self, payload):
        """Ensure that the payload values are valid."""
        # Example validations (adjust as needed for your application)
        
        # Check that required keys are present
        required_keys = ["glitches", "item_placement", "dungeon_items", "accessibility", "goal", "crystals", "mode", "hints", "weapons", "item", "tournament", "spoilers", "lang", "enemizer"]
        
        for key in required_keys:
            if key not in payload:
                self.show_message(f"Missing required setting: {key}")
                raise ValueError(f"Missing required setting: {key}")
        
        # Validate 'crystals' structure
        if "crystals" in payload:
            if not isinstance(payload["crystals"], dict) or "ganon" not in payload["crystals"] or "tower" not in payload["crystals"]:
                self.show_message("Invalid 'crystals' configuration.")
                raise ValueError("Invalid 'crystals' configuration.")
        
        # Validate 'item' settings
        if "item" in payload:
            if not isinstance(payload["item"], dict) or "pool" not in payload["item"] or "functionality" not in payload["item"]:
                self.show_message("Invalid 'item' configuration.")
                raise ValueError("Invalid 'item' configuration.")
        
        # Validate 'enemizer' settings
        if "enemizer" in payload:
            required_enemizer_keys = ["boss_shuffle", "enemy_shuffle", "enemy_damage", "enemy_health"]
            for key in required_enemizer_keys:
                if key not in payload["enemizer"]:
                    self.show_message(f"Missing enemizer setting: {key}")
                    raise ValueError(f"Missing enemizer setting: {key}")
        
        # If 'entrances' is present when using Customizer API, raise an error
        if 'entrances' in payload and not self.api_type == "Randomizer":
            self.show_message("Entrance randomization is not supported with the Customizer API.")
            raise ValueError("Entrance randomization is not supported with the Customizer API.")
        



        
    def ensure_item_counts(self, payload):
        # Ensure 'item' and 'count' keys are present
        payload.setdefault('item', {}).setdefault('count', {})

        # Handle unique items in 'eq' to set their count correctly
        for item in set(payload.get('eq', [])):  # Using set to avoid redundant updates
            payload['item']['count'][item] = payload['eq'].count(item)

        # Ensure BossHeartContainer appears at least 3 times in 'eq'
        boss_heart_count = payload.get('eq', []).count('BossHeartContainer')
        if boss_heart_count < 3:
            payload['eq'].extend(['BossHeartContainer'] * (3 - boss_heart_count))

        # Update the count of BossHeartContainer in item['count']
        payload['item']['count']['BossHeartContainer'] = payload['eq'].count('BossHeartContainer')

        # Specific handling for bottles
        bottle_types = ['Bottle', 'BottleWithRedPotion', 'BottleWithGreenPotion', 
                        'BottleWithBluePotion', 'BottleWithBee', 'BottleWithFairy', 'BottleWithGoldBee']
        
        for bottle_type in bottle_types:
            if bottle_type in payload['eq']:
                payload['item']['count'][bottle_type] = payload['eq'].count(bottle_type)

        # Debug output for consistency check
        print("Final item counts:", payload['item']['count'])
        print("Final starting equipment (eq):", payload['eq'])


    def get_api_type(self, preset_name):
        """Get the correct API URL and type based on preset name."""
        if preset_name in self.randomizer_presets:
            return self.randomizer_url, "Randomizer"
        else:
            return self.customizer_url, "Customizer"

    async def generate_seed_with_api(self, payload, preset_name, api_url, api_type):
        try:
            headers = {
                "accept": "application/json",
                "content-type": "application/json"
            }
            async with aiohttp.ClientSession() as session:
                async with session.post(api_url, headers=headers, json=payload) as response:
                    if response.status == 200:
                        data = await response.json()
                        if 'hash' in data:
                            seed_hash = data['hash']
                            permalink = f"https://alttpr.com/h/{seed_hash}"
                            self.permalink_field.setText(permalink)

                            # Log the generated seed to history
                            self.log_seed_history(preset_name, permalink)

                            # Optionally patch the ROM and launch RetroArch
                            if self.patch_checkbox.isChecked():
                                await self.patch_and_launch_rom(seed_hash)
                        else:
                            self.show_message(f"Failed to generate the {api_type} seed for preset '{preset_name}'.")
                    else:
                        error_message = await response.text()
                        print(f"[DEBUG] Server response ({response.status}): {error_message}")
                        self.show_message(f"Failed to generate the seed for preset '{preset_name}'. Server responded with status code {response.status}.")
        except Exception as e:
            self.show_message(f"An error occurred while generating the seed for preset '{preset_name}'.")
            print(f"[DEBUG] Error making POST request to {api_type} API: {e}")

    def open_seed_history_dialog(self):
        """Open a dialog to display the history of generated seeds."""
        history_dialog = QtWidgets.QDialog(self)
        history_dialog.setWindowTitle("Seed History")
        history_dialog.setGeometry(150, 150, 600, 400)

        layout = QtWidgets.QVBoxLayout(history_dialog)

        # Add a scroll area for the text edit widget to make it scrollable
        scroll_area = QtWidgets.QScrollArea()
        scroll_area.setWidgetResizable(True)

        # Create a text browser widget to display the history
        history_text = QtWidgets.QTextBrowser()
        history_text.setReadOnly(True)

        # Load the history from the file and format it
        try:
            with open("seed_history.txt", "r") as file:
                history_content = file.readlines()
                formatted_history = ""
                for line in history_content:
                    parts = line.split("|")

                    # Check if all expected parts are available
                    if len(parts) == 3:
                        preset = parts[0].split("Preset:")[1].strip() if "Preset:" in parts[0] else "N/A"
                        date = parts[1].split("Date:")[1].strip() if "Date:" in parts[1] else "N/A"
                        permalink = parts[2].split("Permalink:")[1].strip() if "Permalink:" in parts[2] else "N/A"

                        formatted_history += (
                            f"<b style='color:#4CAF50;'>Preset:</b> "
                            f"<span>{preset}</span><br>"
                            f"<b style='color:#FF9800;'>Date:</b> "
                            f"<span>{date}</span><br>"
                            f"<b style='color:#03A9F4;'>Permalink:</b> "
                            f"<a href='{permalink}' style='color:#03A9F4;'>{permalink}</a><br><br>"
                        )
                    else:
                        # Log a warning if the line is not formatted correctly
                        print(f"[DEBUG] Skipping malformed line in seed history: {line.strip()}")

                history_text.setHtml(formatted_history if formatted_history else "<b style='color:#FF0000;'>No valid seed history available.</b>")
        except FileNotFoundError:
            history_text.setHtml("<b style='color:#FF0000;'>No seed history available.</b>")

        # Connect the anchorClicked signal to handle permalink clicks and close the dialog
        history_text.anchorClicked.connect(lambda url: self.load_permalink_and_close(url, history_dialog))

        # Set the text browser widget as the scroll area's widget
        scroll_area.setWidget(history_text)

        # Add the scroll area to the layout
        layout.addWidget(scroll_area)

        # Add a close button at the bottom of the dialog
        close_button = QtWidgets.QPushButton("Close")
        close_button.clicked.connect(history_dialog.accept)
        layout.addWidget(close_button)

        history_dialog.exec_()

    def load_permalink_and_close(self, url, dialog):
        """Load the permalink into the main screen permalink field when clicked, and close the dialog."""
        permalink = url.toString()
        self.permalink_field.setText(permalink)
        dialog.accept()  # Close the dialog











    def launch_emotracker(self):
        """Launch EmoTracker."""
        emotracker_path = self.path_inputs["emotracker_path"].text()  # Update key access to dictionary-style

        # Check if EmoTracker path is valid
        if not os.path.exists(emotracker_path):
            self.show_message(f"EmoTracker path is invalid. Please check the input: {emotracker_path}")
            return

        try:

            # Execute the command
            command = f'"{emotracker_path}"'
            print(f"Command to launch EmoTracker: {command}")  # Debugging statement

            subprocess.Popen(command, shell=True)
        except subprocess.SubprocessError as e:
            self.show_message(f"SubprocessError: {e}")
        except Exception as e:
            self.show_message(f"Failed to launch EmoTracker: {e}")


    def terminate_existing_process(self, process_name):
        """Terminate existing processes by name."""
        for proc in psutil.process_iter(['pid', 'name']):
            if process_name.lower() in proc.info['name'].lower():
                try:
                    proc.terminate()
                    proc.wait(timeout=5)
                except Exception as e:
                    self.show_message(f"Unable to terminate {process_name}: {e}")

    def show_message(self, message):
        """Display a message to the user in a message box."""
        msg_box = QtWidgets.QMessageBox()
        msg_box.setText(message)
        msg_box.exec_()

        

class PermalinkPatchDialog(QtWidgets.QDialog):
    def __init__(self, parent):
        super().__init__(parent)
        self.parent = parent

        self.setWindowTitle("Patch from Permalink")
        self.setGeometry(200, 200, 400, 150)

        # Main layout
        layout = QtWidgets.QVBoxLayout()

        # Permalink Input
        self.permalink_label = QtWidgets.QLabel("Enter Seed Permalink:")
        layout.addWidget(self.permalink_label)
        self.permalink_input = QtWidgets.QLineEdit()
        layout.addWidget(self.permalink_input)

        # Patch Button
        self.patch_button = QtWidgets.QPushButton("Patch")
        self.patch_button.clicked.connect(self.accept)
        layout.addWidget(self.patch_button)

        # Set the dialog's layout
        self.setLayout(layout)
        self.seed_hash = None  # Store the seed hash

        self.seed_update_timer = QtCore.QTimer()
        self.seed_update_timer.setSingleShot(True)  # Ensure it's only called once per trigger
        self.seed_update_timer.timeout.connect(self.on_update_seed_info_timeout)

    def on_update_seed_info_timeout(self):
        """Wrapper function to call the async update_and_display_seed_info."""
        asyncio.create_task(self.update_and_display_seed_info())

    def accept(self):
        """Handle acceptance of the dialog by extracting the seed hash."""
        permalink = self.permalink_input.text().strip()
        if not permalink:
            QtWidgets.QMessageBox.warning(self, "Input Error", "Please enter a valid permalink.")
            return

        try:
            # Extract seed hash from permalink
            if "alttpr.com" in permalink:
                # Handle different variations in the URL format
                parts = permalink.split("/")
                if len(parts) >= 5:
                    # Seed hash should be the last part of the URL
                    self.seed_hash = parts[-1]
                    if self.seed_hash:  # Ensure it's not empty
                        super().accept()  # Close dialog with Accepted status
                        return

            QtWidgets.QMessageBox.warning(self, "Input Error", "Please enter a valid permalink URL.")
        except Exception as e:
            QtWidgets.QMessageBox.critical(self, "Input Error", f"Failed to extract seed hash from permalink: {e}")

    def get_seed_hash(self):
        """Return the extracted seed hash."""
        return self.seed_hash


class CustomizePatchDialog(QtWidgets.QDialog):
    def __init__(self, patch_settings, parent=None):
        super().__init__(parent)
        self.patch_settings = patch_settings
        self.parent = parent  # Reference to the main application to call save_config()

        # Set dialog title and adjusted geometry for a wider dialog
        self.setWindowTitle("Customize Patch")
        self.setGeometry(200, 200, 480, 400)  # Adjust dimensions as needed

        # Apply the parent's stylesheet if available
        if parent is not None:
            self.setStyleSheet(parent.styleSheet())

        # Main layout
        main_layout = QtWidgets.QVBoxLayout()

        # Create a grid layout for the options
        grid_layout = QtWidgets.QGridLayout()
        grid_layout.setHorizontalSpacing(20)
        grid_layout.setVerticalSpacing(15)

        # Heart Speed Combo Box
        self.heartspeed_label = QtWidgets.QLabel("Heart Speed:")
        grid_layout.addWidget(self.heartspeed_label, 0, 0)
        self.heartspeed_combo = QtWidgets.QComboBox()
        self.heartspeed_combo.addItems(['off', 'quarter', 'half', 'double', 'normal'])
        self.heartspeed_combo.setCurrentText(self.patch_settings.get("heartspeed", "normal"))
        grid_layout.addWidget(self.heartspeed_combo, 0, 1)

        # Heart Color Combo Box
        self.heartcolor_label = QtWidgets.QLabel("Heart Color:")
        grid_layout.addWidget(self.heartcolor_label, 0, 2)
        self.heartcolor_combo = QtWidgets.QComboBox()
        self.heartcolor_combo.addItems(['red', 'blue', 'green', 'yellow', 'random'])
        self.heartcolor_combo.setCurrentText(self.patch_settings.get("heartcolor", "red"))
        grid_layout.addWidget(self.heartcolor_combo, 0, 3)

        # Sprite Name Label
        self.spritename_label = QtWidgets.QLabel("Sprite:")
        grid_layout.addWidget(self.spritename_label, 1, 0)

        # Sprite Name Combo Box
        self.spritename_combo = QtWidgets.QComboBox()
        list_view = QtWidgets.QListView()
        list_view.setVerticalScrollBarPolicy(QtCore.Qt.ScrollBarAsNeeded)
        self.spritename_combo.setView(list_view)
        grid_layout.addWidget(self.spritename_combo, 1, 1)

        # Sprite Preview QLabel
        self.sprite_width, self.sprite_height = 16, 24  # Original sprite size
        self.preview_scale_factor = 4  # Scale factor for preview
        self.sprite_preview_label = QtWidgets.QLabel()
        self.sprite_preview_label.setFixedSize(
            self.sprite_width * self.preview_scale_factor,
            self.sprite_height * self.preview_scale_factor
        )
        self.sprite_preview_label.setAlignment(QtCore.Qt.AlignCenter)
        self.sprite_preview_label.setStyleSheet("background-color: none;")  # Optional
        grid_layout.addWidget(self.sprite_preview_label, 1, 2, 1, 2)  # Span columns 2 and 3

        # Load sprite data and populate the combo box with icons and names
        self.load_sprites()

        # Connect the combo box change event to update the sprite preview
        self.spritename_combo.currentIndexChanged.connect(self.update_sprite_preview)

        # Menu Speed Combo Box
        self.menu_speed_label = QtWidgets.QLabel("Menu Speed:")
        grid_layout.addWidget(self.menu_speed_label, 2, 0)
        self.menu_speed_combo = QtWidgets.QComboBox()
        self.menu_speed_combo.addItems(['instant', 'fast', 'normal', 'slow'])
        self.menu_speed_combo.setCurrentText(self.patch_settings.get("menu_speed", "normal"))
        grid_layout.addWidget(self.menu_speed_combo, 2, 1)

        # Add the grid layout to the main layout
        main_layout.addLayout(grid_layout)

        # Music, Quick Swap, MSU-1 Resume checkboxes
        checkbox_layout = QtWidgets.QHBoxLayout()
        checkbox_layout.setSpacing(20)
        self.music_checkbox = QtWidgets.QCheckBox("Enable Music")
        self.music_checkbox.setChecked(self.patch_settings.get("music", True))
        checkbox_layout.addWidget(self.music_checkbox)

        self.quickswap_checkbox = QtWidgets.QCheckBox("Enable Quick Swap")
        self.quickswap_checkbox.setChecked(self.patch_settings.get("quickswap", False))
        checkbox_layout.addWidget(self.quickswap_checkbox)

        self.msu1_checkbox = QtWidgets.QCheckBox("Enable MSU-1 Resume")
        self.msu1_checkbox.setChecked(self.patch_settings.get("msu1_resume", True))
        checkbox_layout.addWidget(self.msu1_checkbox)

        # Add the checkbox layout to the main layout
        main_layout.addLayout(checkbox_layout)

        # OK, Save Default, and Cancel buttons
        button_layout = QtWidgets.QHBoxLayout()
        button_layout.setAlignment(QtCore.Qt.AlignRight)
        button_layout.setSpacing(15)

        self.ok_button = QtWidgets.QPushButton("OK")
        self.ok_button.clicked.connect(self.accept)
        button_layout.addWidget(self.ok_button)

        self.save_default_button = QtWidgets.QPushButton("Save as Default")
        self.save_default_button.clicked.connect(self.save_default_settings)
        button_layout.addWidget(self.save_default_button)

        self.cancel_button = QtWidgets.QPushButton("Cancel")
        self.cancel_button.clicked.connect(self.reject)
        button_layout.addWidget(self.cancel_button)

        # Add the button layout to the main layout
        main_layout.addLayout(button_layout)

        # Set the dialog's main layout
        self.setLayout(main_layout)

    def load_sprites(self):
        try:
            # Load sprites from the parent attributes
            spritesheet = self.parent.spritesheet
            sprite_data = self.parent.sprite_data

            if not spritesheet or not sprite_data:
                raise ValueError("[DEBUG] Parent does not have sprite data or spritesheet loaded.")

            # Sprite dimensions and scale factors
            self.sprite_width, self.sprite_height = 16, 24
            self.icon_scale_factor = 2  # For combo box icons
            self.preview_scale_factor = 4  # For preview image

            # Initialize lists
            self.sprite_names = []
            self.sprite_indices = []

            # Add the "Random" option manually (at index 0)
            random_icon_pixmap = self.extract_and_scale_sprite(0, self.icon_scale_factor)
            self.spritename_combo.addItem(QtGui.QIcon(random_icon_pixmap), "Random")
            self.sprite_names.append("Random")
            self.sprite_indices.append(0)

            # Iterate over sprite data starting from index 1
            for idx, sprite in enumerate(sprite_data, start=1):
                name = sprite['name']
                self.sprite_names.append(name)
                self.sprite_indices.append(idx)

                # Extract and scale the icon pixmap
                icon_pixmap = self.extract_and_scale_sprite(idx, self.icon_scale_factor)
                self.spritename_combo.addItem(QtGui.QIcon(icon_pixmap), name)

            # Set current sprite if exists
            current_sprite = self.patch_settings.get("spritename", "Link")
            index = self.spritename_combo.findText(current_sprite)
            if index >= 0:
                self.spritename_combo.setCurrentIndex(index)
            else:
                self.spritename_combo.setCurrentIndex(0)  # Default to "Random"

            # Update the sprite preview initially
            self.update_sprite_preview(self.spritename_combo.currentIndex())

        except Exception as e:
            print(f"[DEBUG] Error loading sprites: {e}")

    def extract_and_scale_sprite(self, sprite_index, scale_factor):
        x = (sprite_index % (self.parent.spritesheet.width() // self.sprite_width)) * self.sprite_width
        y = (sprite_index // (self.parent.spritesheet.width() // self.sprite_width)) * self.sprite_height

        sprite_pixmap = self.parent.spritesheet.copy(x, y, self.sprite_width, self.sprite_height)

        if not sprite_pixmap.isNull():
            # Optionally make the background transparent
            # Scale the pixmap using FastTransformation
            scaled_pixmap = sprite_pixmap.scaled(
                self.sprite_width * scale_factor,
                self.sprite_height * scale_factor,
                QtCore.Qt.KeepAspectRatio,
                QtCore.Qt.FastTransformation
            )
            return scaled_pixmap
        else:
            return QtGui.QPixmap()


    def update_sprite_preview(self, index):
        try:
            if 0 <= index < len(self.sprite_indices):
                sprite_index = self.sprite_indices[index]
                scaled_pixmap = self.extract_and_scale_sprite(sprite_index, self.preview_scale_factor)
                if not scaled_pixmap.isNull():
                    self.sprite_preview_label.setPixmap(scaled_pixmap)
                else:
                    self.sprite_preview_label.clear()
            else:
                self.sprite_preview_label.clear()
        except Exception as e:
            print(f"[DEBUG] Error updating sprite preview: {e}")




    def get_patch_settings(self):
        """Retrieve the selected patch settings."""
        self.patch_settings["heartspeed"] = self.heartspeed_combo.currentText()
        self.patch_settings["heartcolor"] = self.heartcolor_combo.currentText()  # Keep 'random' if selected
        self.patch_settings["spritename"] = self.spritename_combo.currentText()
        self.patch_settings["menu_speed"] = self.menu_speed_combo.currentText()
        self.patch_settings["music"] = self.music_checkbox.isChecked()
        self.patch_settings["quickswap"] = self.quickswap_checkbox.isChecked()
        self.patch_settings["msu1_resume"] = self.msu1_checkbox.isChecked()

        return self.patch_settings

    def save_default_settings(self):
        """Save current settings as the default in the config file."""
        self.get_patch_settings()
        self.parent.patch_settings.update(self.patch_settings)
        self.parent.save_config()
        self.show_message("Patch settings have been saved as default.")

    def show_message(self, message):
        """Display a message to the user in a message box."""
        msg_box = QtWidgets.QMessageBox()
        msg_box.setText(message)
        msg_box.exec_()





class AdvancedCustomizeSeedDialog(QtWidgets.QDialog):
    def __init__(self, preset_folder, parent=None):
        super().__init__(parent)
        self.preset_folder = preset_folder
        self.custom_settings = {}
        self.preset_name = ""
        self.starting_items = []
        self.setting_widgets = {}  # Store references to labels and combo boxes

        self.setWindowTitle("Create Advanced Custom Preset")
        self.setGeometry(200, 200, 600, 600)

        # Layout setup
        main_layout = QtWidgets.QVBoxLayout(self)

        # API selection combo box
        api_layout = QtWidgets.QHBoxLayout()
        api_label = QtWidgets.QLabel("API Type:")
        self.api_combo_box = QtWidgets.QComboBox(self)
        self.api_combo_box.addItems(["Customizer", "Randomizer"])  # Add both API options
        api_layout.addWidget(api_label)
        api_layout.addWidget(self.api_combo_box)
        main_layout.addLayout(api_layout)

        # Connect the combo box change event to toggle_sections
        self.api_combo_box.currentIndexChanged.connect(self.toggle_sections)


        # Preset name input
        preset_name_layout = QtWidgets.QHBoxLayout()
        preset_name_label = QtWidgets.QLabel("Preset Name:")
        self.preset_name_input = QtWidgets.QLineEdit(self)
        preset_name_layout.addWidget(preset_name_label)
        preset_name_layout.addWidget(self.preset_name_input)
        main_layout.addLayout(preset_name_layout)

        # Goal name input
        goal_name_layout = QtWidgets.QHBoxLayout()
        goal_name_label = QtWidgets.QLabel("Goal Name:")
        self.goal_name_input = QtWidgets.QLineEdit(self)
        goal_name_layout.addWidget(goal_name_label)
        goal_name_layout.addWidget(self.goal_name_input)
        main_layout.addLayout(goal_name_layout)

        # Description input
        description_layout = QtWidgets.QHBoxLayout()
        description_label = QtWidgets.QLabel("Description:")
        self.description_input = QtWidgets.QTextEdit(self)
        self.description_input.setFixedHeight(100)  # Set a fixed height
        # Alternatively, use setMaximumHeight if you want it to be resizable up to a limit
        # self.description_input.setMaximumHeight(100)
        description_layout.addWidget(description_label)
        description_layout.addWidget(self.description_input)
        main_layout.addLayout(description_layout)

        # Create grid layout for settings
        settings_layout = QtWidgets.QGridLayout()
        settings_layout.setHorizontalSpacing(20)
        settings_layout.setVerticalSpacing(10)

        # Updated settings_options dictionary
        settings_options = {
            "glitches": ["none"],
            "item_placement": ["advanced", "basic"],
            "dungeon_items": ["standard", "mc", "mcs", "full"],
            "accessibility": ["items", "locations", "none"],
            "crystals_ganon": ["7", "6", "5", "4", "3", "2", "1", "0", "random"],
            "crystals_tower": ["7", "6", "5", "4", "3", "2", "1", "0", "random"],
            "boss_shuffle": ["none", "simple", "full", "random"],
            "enemy_shuffle": ["none", "shuffled", "random"],
            "enemy_damage": ["default", "shuffled", "random"],
            "enemy_health": ["default", "easy", "hard", "expert"],
            "goal": ["ganon", "fast_ganon", "pedestal", "completionist", "dungeons"],
            "hints": ["on", "off"],
            "item_pool": ["normal", "hard", "expert"],
            "item_functionality": ["normal", "hard", "expert"],
            "lang": ["en", "fr", "de"],
            "mode": ["open", "standard", "inverted", "retro"],
            "entrances": ["none", "simple", "restricted", "full", "crossed"],
            "spoilers": ["on", "off"],
            "tournament": ["false", "true"],
            "weapons": ["randomized", "assured", "vanilla"]
        }

        self.setting_inputs = {}
        self.setting_widgets = {}  # Store references to labels and combo boxes
        row = 0
        col = 0
        max_columns = 3

        for setting, options in settings_options.items():
            label = QtWidgets.QLabel(f"{setting.replace('_', ' ').capitalize()}:")
            combo_box = QtWidgets.QComboBox(self)
            combo_box.addItems(options)
            self.setting_inputs[setting] = combo_box

            settings_layout.addWidget(label, row, col * 2)
            settings_layout.addWidget(combo_box, row, col * 2 + 1)

            # Store label and combo box for later use
            self.setting_widgets[setting] = (label, combo_box)

            col += 1
            if col >= max_columns:
                col = 0
                row += 1

        main_layout.addLayout(settings_layout)

        # Starting items section
        self.starting_items_label = QtWidgets.QLabel("Starting Items:")
        main_layout.addWidget(self.starting_items_label)

        # Create a widget to hold the starting items and additional items
        self.items_widget = QtWidgets.QWidget()
        self.items_widget.setSizePolicy(QtWidgets.QSizePolicy.Preferred, QtWidgets.QSizePolicy.Fixed)

        # Starting items outer layout
        self.starting_items_outer_layout = QtWidgets.QHBoxLayout(self.items_widget)
        self.starting_items_outer_layout.setSpacing(0)
        self.starting_items_outer_layout.setContentsMargins(0, 0, 0, 0)

        # Additional items layout
        self.additional_items_layout = QtWidgets.QGridLayout()
        self.additional_items_layout.setSpacing(0)
        self.additional_items_layout.setContentsMargins(0, 0, 0, 0)
        self.starting_items_outer_layout.addLayout(self.additional_items_layout)

        # Starting items layout
        self.starting_items_layout = QtWidgets.QGridLayout()
        self.starting_items_layout.setSpacing(0)
        self.starting_items_layout.setContentsMargins(0, 0, 0, 0)
        self.starting_items_outer_layout.addLayout(self.starting_items_layout)


        # Add the items_widget to the main layout
        main_layout.addWidget(self.items_widget)

        # Add progressive mail, bottles, hearts, etc.
        additional_items_list = [
            "ProgressiveSword",
            "MoonPearl",
            "ProgressiveMail",  # No armor, Blue Mail, Red Mail
            "ProgressiveShield",  # No shield, Blue Shield, Red Shield, Mirror Shield
            "Bottle1",  # First bottle progression
            "Bottle2",  # Second bottle progression
            "Bottle3",  # Third bottle progression
            "Bottle4",  # Fourth bottle progression
            "BossHeartContainer"    # No extra heart container, 1, 2, ..., max
        ]

        # Icon paths for different progressive items in the left group
        self.additional_items_icons = {
            "ProgressiveSword": [
                resource_path("images/sworddisabled.png"), resource_path("images/sword1.png"), resource_path("images/sword2.png"),
                resource_path("images/sword3.png"), resource_path("images/sword4.png")
            ],
            "MoonPearl": [
                resource_path("images/moonpearldisabled.png"), resource_path("images/moonpearl.png")  
            ],
            "ProgressiveMail": [
                resource_path("images/greenmail.png"), resource_path("images/bluemail.png"), resource_path("images/redmail.png")
            ],
            "ProgressiveShield": [
                resource_path("images/shielddisabled.png"), resource_path("images/blueshield.png"), resource_path("images/redshield.png"), resource_path("images/mirrorshield.png")
            ],
            "Bottle1": [
                resource_path("images/bottledisabled.png"),  resource_path("images/bottle.png"), resource_path("images/bottlewithred.png"),
                resource_path("images/bottlewithgreen.png"), resource_path("images/bottlewithblue.png"), resource_path("images/bottlewithbee.png"),
                resource_path("images/bottlewithgoldbee.png"), resource_path("images/bottlewithfairy.png")
            ],
            "Bottle2": [
                resource_path("images/bottledisabled.png"),  resource_path("images/bottle.png"), resource_path("images/bottlewithred.png"),
                resource_path("images/bottlewithgreen.png"), resource_path("images/bottlewithblue.png"), resource_path("images/bottlewithbee.png"),
                resource_path("images/bottlewithgoldbee.png"), resource_path("images/bottlewithfairy.png")
            ],
            "Bottle3": [
                resource_path("images/bottledisabled.png"),  resource_path("images/bottle.png"), resource_path("images/bottlewithred.png"),
                resource_path("images/bottlewithgreen.png"), resource_path("images/bottlewithblue.png"), resource_path("images/bottlewithbee.png"),
                resource_path("images/bottlewithgoldbee.png"), resource_path("images/bottlewithfairy.png")
            ],
            "Bottle4": [
                resource_path("images/bottledisabled.png"),  resource_path("images/bottle.png"), resource_path("images/bottlewithred.png"),
                resource_path("images/bottlewithgreen.png"), resource_path("images/bottlewithblue.png"), resource_path("images/bottlewithbee.png"),
                resource_path("images/bottlewithgoldbee.png"), resource_path("images/bottlewithfairy.png")
            ],
            "BossHeartContainer": [
                resource_path("images/Bossheartcontainer.png"), resource_path("images/Bossheartcontainer.png")
            ]
        }

        # Set the maximum number of columns for the grid layout
        max_columns = 2  # Set this to the number of columns you want in the grid

        # Add buttons for the additional items to the grid
        self.additional_items_buttons = {}
        row = 0
        col = 0  # Initialize row and column tracking

        for item in additional_items_list:
            item_button = QtWidgets.QPushButton()
            item_button.setIcon(QtGui.QIcon(self.additional_items_icons[item][0]))
            item_button.setIconSize(QtCore.QSize(48, 48))
            item_button.setCheckable(True)
            item_button.setFixedSize(60, 60)
            item_button.setObjectName("additionalItemButton")

            # Initialize state
            self.additional_items_buttons[item] = {"button": item_button, "state": 0}
            item_button.clicked.connect(lambda checked, btn=item_button, itm=item: self.toggle_additional_progressive_item(btn, itm))

            # Add the button to the grid at the current row and column
            self.additional_items_layout.addWidget(item_button, row, col)

            # Special handling for BossHeartContainer
            if item == "BossHeartContainer":
                # Add the combo box next to the BossHeartContainer button
                self.boss_heart_count_combo = QtWidgets.QComboBox()
                self.boss_heart_count_combo.addItems([str(i) for i in range(3, 15)])  # Set a max of 14 containers
                self.boss_heart_count_combo.setVisible(False)  # Initially hidden
                self.boss_heart_count_combo.setFixedWidth(50)  # Adjust the width of the combo box to make it smaller

                # Place the combo box in the grid
                col += 1
                self.additional_items_layout.addWidget(self.boss_heart_count_combo, row, col)
            else:
                # Update the column and row for the next item
                col += 1
                if col >= max_columns:
                    col = 0  # Reset column to 0
                    row += 1  # Move to the next row

        # Add starting items (you can adjust this section as needed)
        self.starting_items_buttons = {}
        self.progressive_items_state = {}
        self.progressive_items_max_states = {
            "ProgressiveSword": 4,
            "ProgressiveGlove": 2,
            "ProgressiveBow": 2,
            "Boomerang": 3
        }

        # Icon paths for different progressive items in the right group
        self.progressive_items_icons = {
            "ProgressiveGlove": [
                resource_path("images/glovedisabled.png"), resource_path("images/glove.png"), resource_path("images/titanmitt.png")
            ],
            "ProgressiveBow": [
                resource_path("images/bowdisabled.png"), resource_path("images/bow.png"), resource_path("images/silvers.png")
            ],            
            "Boomerang": [
                resource_path("images/redboomerang.png"), resource_path("images/redboomerang.png"), resource_path("images/blueboomerang.png"), resource_path("images/bothboomerangs.png")
            ]
        }

        starting_items_list = [
            "ProgressiveBow",
            "Boomerang",
            "Hookshot",
            "Mushroom",
            "Powder",
            "FireRod",
            "IceRod",
            "Bombos",
            "Ether",
            "Quake",
            "Lamp",
            "Hammer",
            "Shovel",
            "BugCatchingNet",
            "BookOfMudora",
            "BLANK",  # Placeholder item
            "CaneOfSomaria",
            "CaneOfByrna",
            "Cape",
            "MagicMirror",
            "PegasusBoots",
            "ProgressiveGlove",
            "Flippers",
            "OcarinaInactive"
        ]

        row = 0
        col = 0
        max_columns = 5  # Number of columns for the grid layout

        for item in starting_items_list:
            if item == "BLANK":
                # Add a non-clickable placeholder QLabel
                placeholder_label = QtWidgets.QLabel("")
                placeholder_label.setFixedSize(60, 60)
                self.starting_items_layout.addWidget(placeholder_label, row, col)
            else:
                item_button = QtWidgets.QPushButton()
                if item in self.progressive_items_max_states:
                    initial_icon_path = self.progressive_items_icons[item][0]
                    item_button.setIcon(QtGui.QIcon(initial_icon_path))
                else:
                    item_button.setIcon(QtGui.QIcon(resource_path(f'images/{item}.png')))

                item_button.setIconSize(QtCore.QSize(48, 48))
                item_button.setCheckable(True)
                item_button.setFixedSize(60, 60)
                item_button.setObjectName("startingItemButton")

                # Set initial grayscale effect
                effect = QtWidgets.QGraphicsColorizeEffect()
                effect.setColor(QtGui.QColor(0, 0, 0))
                effect.setStrength(1.0)
                item_button.setGraphicsEffect(effect)

                # Custom logic for progressive items
                if item in self.progressive_items_max_states:
                    item_button.clicked.connect(lambda checked, btn=item_button, itm=item: self.toggle_progressive_item(btn, itm))
                    self.starting_items_buttons[item] = {"button": item_button, "state": 0}
                else:
                    item_button.clicked.connect(lambda checked, btn=item_button: self.toggle_item_effect(btn))
                    self.starting_items_buttons[item] = item_button

                self.starting_items_layout.addWidget(item_button, row, col)

            col += 1
            if col >= max_columns:
                col = 0
                row += 1

        self.randomizer_settings = {
            "glitches",
            "item_placement",
            "dungeon_items",
            "accessibility",
            "goal",
            "crystals_ganon",
            "crystals_tower",
            "mode",
            "entrances",
            "hints",
            "weapons",
            "item_pool",
            "item_functionality",
            "tournament",
            "spoilers",
            "lang",
            "boss_shuffle",
            "enemy_shuffle",
            "enemy_damage",
            "enemy_health"
        }

        button_layout = QtWidgets.QHBoxLayout()
        self.ok_button = QtWidgets.QPushButton("OK")
        self.ok_button.clicked.connect(self.accept)
        self.load_button = QtWidgets.QPushButton("Load Preset") 
        self.load_button.clicked.connect(self.load_preset)
        self.cancel_button = QtWidgets.QPushButton("Cancel")
        self.cancel_button.clicked.connect(self.reject)

        button_layout.addWidget(self.ok_button)
        button_layout.addWidget(self.load_button) 
        button_layout.addWidget(self.cancel_button)
        main_layout.addLayout(button_layout)

    def load_preset(self):
        """Load a preset from the preset folder and populate the dialog with its settings."""
        options = QtWidgets.QFileDialog.Options()
        options |= QtWidgets.QFileDialog.DontUseNativeDialog
        preset_file, _ = QtWidgets.QFileDialog.getOpenFileName(
            self,
            "Load Preset",
            self.preset_folder,
            "Preset Files (*.json *.yaml *.yml)",
            options=options
        )

        if preset_file:
            # Determine the file type based on the extension
            file_type = 'json' if preset_file.endswith('.json') else 'yaml'
            
            # Load the preset file
            try:
                with open(preset_file, 'r') as file:
                    preset_data = json.load(file) if file_type == 'json' else yaml.safe_load(file)
            except Exception as e:
                QtWidgets.QMessageBox.warning(self, "Error", f"Failed to load the preset file.\n{e}")
                return

            # Populate the dialog with the preset data
            self.populate_from_preset(preset_data)
            self.toggle_sections()  # Ensure sections are updated correctly



    def populate_from_preset(self, preset_data):
        """Populate the dialog with the settings from the loaded preset."""
        # Set the API type
        if 'entrances' in preset_data and preset_data.get('entrances') != 'none':
            index = self.api_combo_box.findText("Randomizer")
            if index != -1:
                self.api_combo_box.setCurrentIndex(index)
        else:
            index = self.api_combo_box.findText("Customizer")
            if index != -1:
                self.api_combo_box.setCurrentIndex(index)

        # Call toggle_sections to update the UI
        self.toggle_sections()
        
        # Populate the settings combo boxes
        for setting, combo_box in self.setting_inputs.items():
            value = self.get_nested_value(preset_data, setting)
            if value is not None:
                value_str = str(value)
                index = combo_box.findText(value_str)
                if index != -1:
                    combo_box.setCurrentIndex(index)
                else:
                    # Add the value if it's not in the combo box options
                    combo_box.addItem(value_str)
                    combo_box.setCurrentText(value_str)
            else:
                # Set to default value if available
                combo_box.setCurrentIndex(0)
        
        # Populate the preset name and description
        self.preset_name_input.setText(preset_data.get("name", ""))
        self.description_input.setPlainText(preset_data.get("notes", ""))
        
        # Populate starting items
        eq_list = preset_data.get("eq", [])
        if not isinstance(eq_list, list):
            eq_list = []
        self.populate_starting_items(eq_list)
        
        # Handle additional items if applicable
        if self.api_combo_box.currentText() == "Customizer":
            self.populate_additional_items(eq_list)


    
    def get_nested_value(self, data, key):
        """Retrieve a nested value from the preset data based on the setting key."""
        if key in data:
            return data[key]
        elif key == 'crystals_ganon':
            ganon_value = data.get('crystals', {}).get('ganon')
            return str(ganon_value) if ganon_value is not None else None
        elif key == 'crystals_tower':
            tower_value = data.get('crystals', {}).get('tower')
            return str(tower_value) if tower_value is not None else None
        elif key in ['item_pool', 'item_functionality']:
            return data.get('item', {}).get(key.split('_')[1])
        elif key in ['boss_shuffle', 'enemy_shuffle', 'enemy_damage', 'enemy_health']:
            return data.get('enemizer', {}).get(key)
        elif key == 'tournament':
            tournament_value = data.get('tournament', False)
            if isinstance(tournament_value, bool):
                return 'true' if tournament_value else 'false'
            elif isinstance(tournament_value, str):
                return tournament_value.lower()
            else:
                return 'false'
        elif key == 'spoilers':
            spoilers_value = data.get('spoilers', 'on')
            return str(spoilers_value).lower()
        else:
            return None




    def toggle_sections(self):
        """Toggle visibility of starting items and additional items based on API selection."""
        if self.api_combo_box.currentText() == "Randomizer":
            self.starting_items_label.hide()
            self.items_widget.hide()
            # Hide settings not in Randomizer API
            for setting, widgets in self.setting_widgets.items():
                if setting not in self.randomizer_settings:
                    widgets[0].hide()  # Hide label
                    widgets[1].hide()  # Hide combo box
                else:
                    widgets[0].show()
                    widgets[1].show()
        else:
            self.starting_items_label.show()
            self.items_widget.show()
            # Show all settings except 'entrances'
            for setting, widgets in self.setting_widgets.items():
                if setting == 'entrances':
                    widgets[0].hide()  # Hide label
                    widgets[1].hide()  # Hide combo box
                else:
                    widgets[0].show()
                    widgets[1].show()
        # Adjust the dialog size after toggling
        self.adjustSize()



    def toggle_item_effect(self, button):
        """Toggle item image between grayscale and full color when checked/unchecked."""
        effect = button.graphicsEffect()
        if button.isChecked():
            effect.setEnabled(False)  # Remove grayscale effect
        else:
            effect.setEnabled(True)  # Apply grayscale effect

    def toggle_progressive_item(self, button, item, set_state=None):
        """Handle the cycling state of progressive items like swords, gloves, and bows."""
        if item not in self.starting_items_buttons:
            return

        if set_state is not None:
            next_state = set_state
        else:
            current_state = self.starting_items_buttons[item]["state"]
            max_state = self.progressive_items_max_states.get(item, 1)
            next_state = (current_state + 1) % (max_state + 1)  # Cycle through states

        self.starting_items_buttons[item]["state"] = next_state

        # Update button icon
        icon_path = self.progressive_items_icons.get(item, [resource_path(f'images/{item}.png')])[next_state]
        button.setIcon(QtGui.QIcon(icon_path))

        # Update checked state
        button.setChecked(next_state != 0)
        self.toggle_item_effect(button)


    def populate_starting_items(self, eq_list):
        """Populate starting items based on the 'eq' list from the preset."""
        # Reset all starting items
        for item, button_data in self.starting_items_buttons.items():
            if isinstance(button_data, dict) and "state" in button_data:
                # Reset progressive items
                self.toggle_progressive_item(button_data["button"], item, set_state=0)
            else:
                button_data.setChecked(False)
                self.toggle_item_effect(button_data)

        # Set items based on eq_list
        for item in eq_list:
            if item in self.starting_items_buttons:
                button_data = self.starting_items_buttons[item]
                if isinstance(button_data, dict) and "state" in button_data:
                    if item == "ProgressiveSword":
                        state = min(eq_list.count("ProgressiveSword"), self.progressive_items_max_states.get(item, 1))
                        self.toggle_progressive_item(button_data["button"], item, set_state=state)
                    elif item == "Boomerang":
                        state = 1 if "RedBoomerang" in eq_list else 2 if "Boomerang" in eq_list else 3
                        self.toggle_progressive_item(button_data["button"], item, set_state=state)
                else:
                    button_data.setChecked(True)
                    self.toggle_item_effect(button_data)

            # Process the 'eq' list
            for item in eq_list:
                if item in self.starting_items_buttons:
                    button_data = self.starting_items_buttons[item]
                    if isinstance(button_data, dict) and "state" in button_data:
                        # Handle progressive items
                        if item == "ProgressiveSword":
                            button_data["state"] += 1
                            max_state = self.progressive_items_max_states.get(item, 1)
                            if button_data["state"] > max_state:
                                button_data["state"] = max_state
                            self.toggle_progressive_item(button_data["button"], item, set_state=button_data["state"])
                        elif item == "Boomerang":
                            # Handle the different boomerang states
                            if item == "Boomerang" and item in eq_list:
                                button_data["state"] = 1
                                self.toggle_progressive_item(button_data["button"], item, set_state=1)
                        else:
                            # Set state to 1
                            button_data["state"] = 1
                            self.toggle_progressive_item(button_data["button"], item, set_state=1)
                else:
                    # Handle special cases not directly in starting_items_buttons
                    if item == "Bow":
                        button_data = self.starting_items_buttons.get("ProgressiveBow")
                        if button_data:
                            button_data["state"] = 1
                            self.toggle_progressive_item(button_data["button"], "ProgressiveBow", set_state=1)
                    elif item == "BowAndSilverArrows":
                        button_data = self.starting_items_buttons.get("ProgressiveBow")
                        if button_data:
                            button_data["state"] = 2
                            self.toggle_progressive_item(button_data["button"], "ProgressiveBow", set_state=2)
                    elif item == "PowerGlove":
                        button_data = self.starting_items_buttons.get("ProgressiveGlove")
                        if button_data:
                            button_data["state"] = 1
                            self.toggle_progressive_item(button_data["button"], "ProgressiveGlove", set_state=1)
                    elif item == "TitansMitt":
                        button_data = self.starting_items_buttons.get("ProgressiveGlove")
                        if button_data:
                            button_data["state"] = 2
                            self.toggle_progressive_item(button_data["button"], "ProgressiveGlove", set_state=2)




    def populate_additional_items(self, eq_list):
        """Populate additional items based on the 'eq' list from the preset."""
        # Reset all additional items
        for item, button_data in self.additional_items_buttons.items():
            button_data["state"] = 0
            button_data["button"].setChecked(False)
            self.toggle_additional_progressive_item(button_data["button"], item, set_state=0)

        # Initialize bottle counts
        bottle_counts = {
            "Bottle": 0,
            "BottleWithRedPotion": 0,
            "BottleWithGreenPotion": 0,
            "BottleWithBluePotion": 0,
            "BottleWithBee": 0,
            "BottleWithGoldBee": 0,
            "BottleWithFairy": 0
        }

        # Process the 'eq' list
        for item in eq_list:
            if item.startswith("Bottle"):
                bottle_counts[item] += 1
            elif item == "ProgressiveMail":
                button_data = self.additional_items_buttons.get("ProgressiveMail")
                if button_data:
                    button_data["state"] += 1
                    max_state = len(self.additional_items_icons["ProgressiveMail"]) - 1
                    if button_data["state"] > max_state:
                        button_data["state"] = max_state
                    self.toggle_additional_progressive_item(button_data["button"], "ProgressiveMail", set_state=button_data["state"])
            elif item == "ProgressiveShield":
                button_data = self.additional_items_buttons.get("ProgressiveShield")
                if button_data:
                    button_data["state"] += 1
                    max_state = len(self.additional_items_icons["ProgressiveShield"]) - 1
                    if button_data["state"] > max_state:
                        button_data["state"] = max_state
                    self.toggle_additional_progressive_item(button_data["button"], "ProgressiveShield", set_state=button_data["state"])
            elif item == "MoonPearl":
                button_data = self.additional_items_buttons.get("MoonPearl")
                if button_data:
                    button_data["state"] = 1
                    self.toggle_additional_progressive_item(button_data["button"], "MoonPearl", set_state=1)
            elif item == "BossHeartContainer":
                button_data = self.additional_items_buttons.get("BossHeartContainer")
                if button_data:
                    button_data["state"] = 1
                    count = eq_list.count("BossHeartContainer")
                    self.boss_heart_count_combo.setCurrentText(str(count))
                    self.toggle_additional_progressive_item(button_data["button"], "BossHeartContainer", set_state=1)

        # Assign bottles to Bottle1, Bottle2, etc.
        bottle_items = ["Bottle1", "Bottle2", "Bottle3", "Bottle4"]
        bottle_index = 0
        for bottle_type, count in bottle_counts.items():
            for _ in range(count):
                if bottle_index >= len(bottle_items):
                    break  # No more bottle slots
                item = bottle_items[bottle_index]
                button_data = self.additional_items_buttons.get(item)
                if button_data:
                    # Determine the state based on bottle_type
                    bottle_states = {
                        "Bottle": 1,
                        "BottleWithRedPotion": 2,
                        "BottleWithGreenPotion": 3,
                        "BottleWithBluePotion": 4,
                        "BottleWithBee": 5,
                        "BottleWithGoldBee": 6,
                        "BottleWithFairy": 7
                    }
                    state = bottle_states.get(bottle_type, 1)
                    button_data["state"] = state
                    self.toggle_additional_progressive_item(button_data["button"], item, set_state=state)
                bottle_index += 1




    def toggle_additional_progressive_item(self, button, item, set_state=None):
        """Handle the cycling state of additional progressive items like mail, bottles, and hearts."""
        if set_state is not None:
            next_state = set_state
        else:
            current_state = self.additional_items_buttons[item]["state"]
            max_state = len(self.additional_items_icons[item]) - 1
            next_state = (current_state + 1) % (max_state + 1)  # Cycle through states

        self.additional_items_buttons[item]["state"] = next_state

        # Update button icon
        icon_path = self.additional_items_icons[item][next_state]
        button.setIcon(QtGui.QIcon(icon_path))

        # Update checked state
        button.setChecked(next_state != 0)

        # Handle BossHeartContainer combo box visibility
        if item == "BossHeartContainer":
            if next_state > 0:
                self.boss_heart_count_combo.setVisible(True)
            else:
                self.boss_heart_count_combo.setVisible(False)




    def get_custom_settings(self):
        """Retrieve the selected custom settings."""
        api_type = self.api_combo_box.currentText()

        if api_type == "Randomizer":
            # Build custom_settings for Randomizer API
            self.custom_settings = {
                "glitches": self.setting_inputs.get("glitches").currentText(),
                "item_placement": self.setting_inputs.get("item_placement").currentText(),
                "dungeon_items": self.setting_inputs.get("dungeon_items").currentText(),
                "accessibility": self.setting_inputs.get("accessibility").currentText(),
                "crystals": {
                    "ganon": self.setting_inputs.get("crystals_ganon").currentText(),
                    "tower": self.setting_inputs.get("crystals_tower").currentText()
                },
                "goal": self.setting_inputs.get("goal").currentText(),
                "mode": self.setting_inputs.get("mode").currentText(),
                "entrances": self.setting_inputs.get("entrances").currentText(),
                "hints": self.setting_inputs.get("hints").currentText(),
                "weapons": self.setting_inputs.get("weapons").currentText(),
                "item": {
                    "pool": self.setting_inputs.get("item_pool").currentText(),
                    "functionality": self.setting_inputs.get("item_functionality").currentText()
                },
                "tournament": self.setting_inputs.get("tournament").currentText() == "true",
                "spoilers": self.setting_inputs.get("spoilers").currentText(),
                "lang": self.setting_inputs.get("lang").currentText(),
                "enemizer": {
                    "boss_shuffle": self.setting_inputs.get("boss_shuffle").currentText(),
                    "enemy_shuffle": self.setting_inputs.get("enemy_shuffle").currentText(),
                    "enemy_damage": self.setting_inputs.get("enemy_damage").currentText(),
                    "enemy_health": self.setting_inputs.get("enemy_health").currentText()
                }
            }
        else:
            # Build custom_settings for Customizer API
            self.custom_settings = {
                "glitches": self.setting_inputs.get("glitches").currentText(),
                "item_placement": self.setting_inputs.get("item_placement").currentText(),
                "dungeon_items": self.setting_inputs.get("dungeon_items").currentText(),
                "accessibility": self.setting_inputs.get("accessibility").currentText(),
                "crystals": {
                    "ganon": self.setting_inputs.get("crystals_ganon").currentText(),
                    "tower": self.setting_inputs.get("crystals_tower").currentText()
                },
                "goal": self.setting_inputs.get("goal").currentText(),
                "mode": self.setting_inputs.get("mode").currentText(),
                "hints": self.setting_inputs.get("hints").currentText(),
                "weapons": self.setting_inputs.get("weapons").currentText(),
                "item": {
                    "pool": self.setting_inputs.get("item_pool").currentText(),
                    "functionality": self.setting_inputs.get("item_functionality").currentText()
                },
                "tournament": self.setting_inputs.get("tournament").currentText() == "true",
                "spoilers": self.setting_inputs.get("spoilers").currentText(),
                "lang": self.setting_inputs.get("lang").currentText(),
                "enemizer": {
                    "boss_shuffle": self.setting_inputs.get("boss_shuffle").currentText(),
                    "enemy_shuffle": self.setting_inputs.get("enemy_shuffle").currentText(),
                    "enemy_damage": self.setting_inputs.get("enemy_damage").currentText(),
                    "enemy_health": self.setting_inputs.get("enemy_health").currentText()
                },
                "name": self.preset_name_input.text().strip(),
                "notes": self.description_input.toPlainText().strip(),
                "l": {},
                "eq": []  # To store starting items
            }

        for item, button_data in self.starting_items_buttons.items():
            if isinstance(button_data, dict) and "state" in button_data:
                state = button_data["state"]
                # Handle progressive items based on state
                if item == "ProgressiveSword" and state > 0:
                    self.custom_settings["eq"].extend(["ProgressiveSword"] * state)
                elif item == "ProgressiveGlove" and state > 0:
                    self.custom_settings["eq"].extend(["ProgressiveGlove"] * state)
                elif item == "Boomerang":
                    # Add boomerang items based on state
                    if state == 1:
                        self.custom_settings["eq"].append("RedBoomerang")
                    elif state == 2:
                        self.custom_settings["eq"].append("Boomerang")
                    elif state == 3:
                        self.custom_settings["eq"].extend(["RedBoomerang", "Boomerang"])
            else:
                # Handle non-progressive starting items
                if button_data.isChecked():
                    self.custom_settings["eq"].append(item)

        # Add additional progressive items
        for item, button_data in self.additional_items_buttons.items():
            state = button_data["state"]
            if item == "BossHeartContainer":
                if button_data["button"].isChecked():
                    count = int(self.boss_heart_count_combo.currentText())
                    self.custom_settings["eq"].extend(["BossHeartContainer"] * count)
            elif state > 0:
                if item == "ProgressiveMail":
                    self.custom_settings["eq"].extend(["ProgressiveArmor"] * state)
                elif item == "ProgressiveShield":
                    self.custom_settings["eq"].extend(["ProgressiveShield"] * state)
                elif item.startswith("Bottle"):
                    bottle_type = {
                        1: "Bottle",
                        2: "BottleWithRedPotion",
                        3: "BottleWithGreenPotion",
                        4: "BottleWithBluePotion",
                        5: "BottleWithBee",
                        6: "BottleWithGoldBee",
                        7: "BottleWithFairy"
                    }.get(state, "Bottle")
                    self.custom_settings["eq"].append(bottle_type)
                elif item == "ProgressiveSword" and state > 0:
                    self.custom_settings["eq"].extend(["ProgressiveSword"] * state)
                elif item == "MoonPearl":
                    if state == 1:
                        self.custom_settings["eq"].append("MoonPearl")


        if api_type == "Customizer":
            # Add "drops" section
            self.custom_settings["drops"] = {
                "0": ["auto_fill"] * 8,
                "1": ["auto_fill"] * 8,
                "2": ["auto_fill"] * 8,
                "3": ["auto_fill"] * 8,
                "4": ["auto_fill"] * 8,
                "5": ["auto_fill"] * 8,
                "6": ["auto_fill"] * 8,
                "pull": ["auto_fill", "auto_fill", "auto_fill"],
                "crab": ["auto_fill", "auto_fill"],
                "stun": ["auto_fill"],
                "fish": ["auto_fill"]
            }

            # Add "custom" section
            self.custom_settings["custom"] = {
                "item.Goal.Required": "",
                "item.require.Lamp": False,
                "item.value.BlueClock": "",
                "item.value.GreenClock": "",
                "item.value.RedClock": "",
                "item.value.Rupoor": "",
                "prize.crossWorld": True,
                "prize.shuffleCrystals": True,
                "prize.shufflePendants": True,
                "region.bossNormalLocation": True,
                "region.wildBigKeys": False,
                "region.wildCompasses": False,
                "region.wildKeys": False,
                "region.wildMaps": False,
                "rom.dungeonCount": "off",
                "rom.freeItemMenu": False,
                "rom.freeItemText": False,
                "rom.mapOnPickup": False,
                "rom.timerMode": "off",
                "rom.timerStart": "",
                "rom.rupeeBow": False,
                "rom.genericKeys": False,
                "rom.logicMode": "MajorGlitches",
                "spoil.BootsLocation": False,
                "canBootsClip": False,
                "canBunnyRevive": False,
                "canBunnySurf": False,
                "canDungeonRevive": False,
                "canFakeFlipper": False,
                "canMirrorClip": False,
                "canMirrorWrap": False,
                "canTransitionWrapped": False,
                "canOneFrameClipOW": False,
                "canOneFrameClipUW": False,
                "canOWYBA": False,
                "canSuperBunny": False,
                "canSuperSpeed": False,
                "canWaterWalk": False,
                "item": {
                    "count": {
                        "BottleWithRandom": 4,
                        "Nothing": 0,
                        "L1Sword": 0,
                        "L1SwordAndShield": 0,
                        "MasterSword": 0,
                        "L3Sword": 0,
                        "L4Sword": 0,
                        "BlueShield": 0,
                        "RedShield": 0,
                        "MirrorShield": 0,
                        "FireRod": 1,
                        "IceRod": 1,
                        "Hammer": 1,
                        "Hookshot": 1,
                        "Bow": 0,
                        "Boomerang": 1,
                        "Powder": 1,
                        "Bombos": 1,
                        "Ether": 1,
                        "Quake": 1,
                        "Lamp": 1,
                        "Shovel": 1,
                        "OcarinaInactive": 1,
                        "CaneOfSomaria": 1,
                        "Bottle": 0,
                        "PieceOfHeart": 24,
                        "CaneOfByrna": 1,
                        "Cape": 1,
                        "MagicMirror": 1,
                        "PowerGlove": 0,
                        "TitansMitt": 0,
                        "BookOfMudora": 1,
                        "Flippers": 1,
                        "MoonPearl": 1,
                        "BugCatchingNet": 1,
                        "BlueMail": 0,
                        "RedMail": 0,
                        "Bomb": 0,
                        "ThreeBombs": 16,
                        "Mushroom": 1,
                        "RedBoomerang": 1,
                        "BottleWithRedPotion": 0,
                        "BottleWithGreenPotion": 0,
                        "BottleWithBluePotion": 0,
                        "TenBombs": 1,
                        "OneRupee": 2,
                        "FiveRupees": 4,
                        "TwentyRupees": 28,
                        "BowAndArrows": 0,
                        "BowAndSilverArrows": 0,
                        "BottleWithBee": 0,
                        "BottleWithFairy": 0,
                        "BossHeartContainer": 10,
                        "HeartContainer": 1,
                        "OneHundredRupees": 1,
                        "FiftyRupees": 7,
                        "Heart": 0,
                        "Arrow": 1,
                        "TenArrows": 12,
                        "SmallMagic": 0,
                        "ThreeHundredRupees": 5,
                        "BottleWithGoldBee": 0,
                        "OcarinaActive": 0,
                        "PegasusBoots": 1,
                        "BombUpgrade5": 0,
                        "BombUpgrade10": 0,
                        "ArrowUpgrade5": 0,
                        "ArrowUpgrade10": 0,
                        "HalfMagic": 1,
                        "QuarterMagic": 0,
                        "SilverArrowUpgrade": 0,
                        "Rupoor": 0,
                        "RedClock": 0,
                        "BlueClock": 0,
                        "GreenClock": 0,
                        "ProgressiveSword": 4,
                        "ProgressiveShield": 3,
                        "ProgressiveArmor": 2,
                        "ProgressiveGlove": 2,
                        "ProgressiveBow": 2,
                        "Triforce": 0,
                        "TriforcePiece": 0
                    }
                },
                "drop": {
                    "count": {
                        "Bee": 0,
                        "BeeGood": 0,
                        "Heart": 13,
                        "RupeeGreen": 9,
                        "RupeeBlue": 7,
                        "RupeeRed": 6,
                        "BombRefill1": 7,
                        "BombRefill4": 1,
                        "BombRefill8": 2,
                        "MagicRefillSmall": 6,
                        "MagicRefillFull": 3,
                        "ArrowRefill5": 5,
                        "ArrowRefill10": 3,
                        "Fairy": 1
                    }
                }
            }

        return self.custom_settings

    def save_preset(self):
        """Save the advanced custom preset to a JSON file."""
        self.get_custom_settings()  # Get current settings
        preset_name = self.get_preset_name()

        if preset_name:
            preset_path = os.path.join(self.preset_folder, f"{preset_name}.json")
            self.save_custom_settings_to_json(preset_path)

    def get_preset_name(self):
        """Get the preset name entered by the user."""
        return self.preset_name_input.text().strip()

    def save_custom_settings_to_json(self, filepath):
        """Save the custom settings to a JSON file."""
        # Ensure we have the latest custom settings before saving
        self.get_custom_settings()

        # Save the JSON data to the specified file path
        with open(filepath, 'w') as json_file:
            json.dump(self.custom_settings, json_file, indent=2)
class GifPopup(QtWidgets.QWidget):
    def __init__(self, gif_url, parent=None):
        super().__init__(parent)
        self.setWindowFlags(QtCore.Qt.FramelessWindowHint | QtCore.Qt.ToolTip)
        self.setAttribute(QtCore.Qt.WA_TranslucentBackground)
        self.label = QtWidgets.QLabel(self)

        # Load the GIF from the URL
        response = requests.get(gif_url)
        if response.status_code == 200:
            temp_gif_path = os.path.join(os.getcwd(), "hover_sprite.gif")
            with open(temp_gif_path, 'wb') as f:
                f.write(response.content)

            # Load the GIF and display it
            self.display_full_gif(temp_gif_path)

        else:
            print(f"Failed to load GIF: {gif_url}")

    def display_full_gif(self, gif_path):
        """Display the full GIF without cropping, using its original size."""
        # Create a QMovie object for the GIF
        movie = QtGui.QMovie(gif_path)
        movie.setScaledSize(QtCore.QSize(192, 192))  # Set to 192x192 size

        # Set the QLabel to display the GIF
        self.label.setMovie(movie)
        movie.start()

        # Set the size of the popup to match the GIF size
        self.setFixedSize(192, 192)
class SpriteLabel(QtWidgets.QLabel):
    def __init__(self, sprite_pixmap, gif_url, parent=None):
        super().__init__(parent)
        self.static_pixmap = sprite_pixmap  # Static sprite image
        self.gif_url = gif_url  # URL for the GIF
        self.gif_popup = None  # Popup window for the GIF

        self.setPixmap(self.static_pixmap)  # Set the static sprite by default
        self.setFixedSize(self.static_pixmap.size())  # Set label size based on static sprite size

    def enterEvent(self, event):
        """Triggered when the mouse hovers over the QLabel."""
        if not self.gif_popup:
            # Create a popup window for the GIF
            self.gif_popup = GifPopup(self.gif_url)
        
        # Show the popup near the cursor
        cursor_pos = QtGui.QCursor.pos()
        self.gif_popup.move(cursor_pos.x() + 20, cursor_pos.y() + 20)  # Position next to the cursor
        self.gif_popup.show()

    def leaveEvent(self, event):
        """Triggered when the mouse leaves the QLabel."""
        if self.gif_popup:
            self.gif_popup.hide()  # Hide the GIF popup

if __name__ == "__main__":
    import sys
    from PyQt5 import QtWidgets
    from qasync import QEventLoop, asyncSlot  # Ensure qasync is installed: pip install qasync

    # Define your get_stylesheet function here or import it
    font_family = "The Legend of Zelda: A Link to "  # Ensure this font is installed or use a fallback

    def get_stylesheet():
        return f"""
            QDialog, QWidget {{
                background-color: #1a1a1a;
                color: #ffffff;  /* White text for better visibility */
                font-size: 14px;
                font-family: '{font_family}';  /* Custom font */
            }}
            QComboBox, QLineEdit {{
                background-color: #2b2b2b;
                border: 2px solid #4a90e2;  /* Matte blue for the borders */
                padding: 6px;
                border-radius: 8px;
                color: #ffffff;
                font-family: '{font_family}';  /* Custom font */
            }}
            QPushButton {{
                background-color: #333333;
                border: 2px solid #4a90e2;  /* Matte blue for the button borders */
                border-radius: 8px;
                padding: 8px;
                color: #4a90e2;
                font-family: '{font_family}';  /* Custom font */
            }}
            QPushButton:hover {{
                background-color: #4a90e2;  /* Matte blue hover effect */
                color: #000000;  /* Black text when hovered */
                font-family: '{font_family}';  /* Custom font */
            }}
            /* Specific style for starting and additional item buttons */
            QPushButton#startingItemButton, QPushButton#additionalItemButton {{
                background-color: transparent;  /* Remove background color */
                border: none;  /* Remove button borders */
            }}
            QPushButton#startingItemButton:hover, QPushButton#additionalItemButton:hover {{
                background-color: #4a90e2;  /* Matte blue hover effect */
                color: #000000;  /* Black text when hovered */
            }}
            QGroupBox {{
                border: 2px solid #4a90e2;  /* Matte blue border for group box */
                border-radius: 12px;
                margin-top: 20px;
                padding: 20px;
                font-family: '{font_family}';  /* Custom font */
            }}
            QGroupBox::title {{
                subcontrol-origin: margin;
                subcontrol-position: top left;
                background-color: transparent;
                color: #4a90e2;  /* Matte blue for the title text */
                padding: 0 10px;
                font-weight: bold;
                font-family: '{font_family}';  /* Custom font */
            }}
            QCheckBox {{
                color: #e0e0e0;  /* Light grey text for better visibility */
                padding: 5px;
            }}
            QCheckBox::indicator {{
                width: 16px;
                height: 16px;
            }}
            QCheckBox::indicator:unchecked {{
                border: 2px solid #4a90e2;  /* Matte blue border for the checkbox */
                background-color: #2b2b2b;
            }}
            QCheckBox::indicator:checked {{
                border: 2px solid #4a90e2;  /* Matte blue border for the checkbox */
                background-color: #4a90e2;  /* Matte blue when checked */
            }}
        """

    # Create the application
    app = QtWidgets.QApplication(sys.argv)
    loop = QEventLoop(app)
    asyncio.set_event_loop(loop)  # Set the event loop for asyncio

    # Apply the stylesheet
    app.setStyleSheet(get_stylesheet())

    # Create and show the main window
    window = ALTTPRSeedGeneratorApp()
    window.show()

    # Run the application event loop with qasync
    with loop:
        loop.run_forever()