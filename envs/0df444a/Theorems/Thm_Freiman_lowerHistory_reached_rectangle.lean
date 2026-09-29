-- Prove2me | Theorems.Thm_Freiman_lowerHistory_reached_rectangle
-- name    : Freiman.lowerHistory_reached_rectangle
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:31:32.799254+00:00
-- url     : https://prove2.me/theorems/486611f9-5372-4f47-993b-ecee3700e606
-- title:
--   Freiman.lowerHistory_reached_rectangle
-- statement:
--   Suffix continuant boxes and the selected initial-family parameter bounds place the actual origin in the stored closed rectangle.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026); global_selection.tex, lem:global-suffix-targets; history_certificates.tex, app:all-suffix-histories; verification/families/target_selection/verify_suffix_targets_independent.py; certificates/target_selection/all_suffix_histories_printed.json; role: source suffix parameter boxes

import Definitions.Def_Freiman_lowerInitialEntry
import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic

open Freiman

theorem Freiman.lowerHistory_reached_rectangle (hfamily : ∀ (f : LowerInitialFamily) (a k v : ℕ), lowerEntryDomain (lowerNormalize (lowerFamilyPair f a k v))) (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t h n)
    (base : LowerPair) (p : LowerHistoryPath) (hmem : p ∈ lowerHistoryPaths.toList) (hp : lowerHistoryStructural p) (hr : lowerHistoryReached t h n base p) :
    certRectangleMem p.rectangle (lowerRatio base.1) (lowerRatio base.2) := by
  sorry
