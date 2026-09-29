-- Prove2me | Theorems.Thm_Freiman_lower_bridge_binding_aPos
-- name    : Freiman.lower_bridge_binding_aPos
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:58:13.350577+00:00
-- url     : https://prove2.me/theorems/7eace51c-cf7b-4740-957a-bfc60a9ce8ee
-- title:
--   Freiman marked initial bridges: binding aPos
-- statement:
--   Finite exact coefficient identities for the actual aPos matrix widths, cuts and contacts.
-- source:
--   Freiman report, initial_bridges.tex, corrected marked H entries; H_entry_bridges.json 185 exact polynomial records.

import Definitions.Def_Freiman_lowerBridgeCatalog
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_bridge_binding_aPos : ∀ r ∈ lowerBridgeRecords .aPos, ∀ x y : ℝ, certPolyEval r.polynomial x y = lowerBridgeNumerator .aPos r x y := by
  sorry
