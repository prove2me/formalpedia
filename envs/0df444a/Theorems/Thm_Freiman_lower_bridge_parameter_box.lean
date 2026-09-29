-- Prove2me | Theorems.Thm_Freiman_lower_bridge_parameter_box
-- name    : Freiman.lower_bridge_parameter_box
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:59:30.227116+00:00
-- url     : https://prove2.me/theorems/b652b8dc-d4bb-4294-893c-ed47626ae336
-- title:
--   Freiman marked initial bridges: parameter box
-- statement:
--   The reached matrix ratios belong to the exact source rectangle.
-- source:
--   Freiman report, initial_bridges.tex, corrected marked H entries; H_entry_bridges.json 185 exact polynomial records.

import Definitions.Def_Freiman_lowerBridgeCatalog
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_bridge_parameter_box (n k : ℕ) : certRectangleMem lowerBridgeRectangle (lowerInitialX n) (lowerInitialY k) := by
  sorry
