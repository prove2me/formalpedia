-- Prove2me | Theorems.Thm_Freiman_lowerHistory_reached_normalizations
-- name    : Freiman.lowerHistory_reached_normalizations
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:31:48.545339+00:00
-- url     : https://prove2.me/theorems/3116d4f4-56a9-4b3b-b2ad-82a8440a9216
-- title:
--   Freiman.lowerHistory_reached_normalizations
-- statement:
--   Incoming orientation is preserved at ties; the forced 20/30/01 steps give strict normalization and other steps give weak normalization.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026); lower_core.tex, eq:lc-difference and eq:lc-full-width; history_certificates.tex, app:all-suffix-histories; verification/families/section15_late/independent_engine.py and verification/families/target_selection/verify_h5_original_independent.py; role: source full-width step comparisons

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic

open Freiman

theorem Freiman.lowerHistory_reached_normalizations (hf : ∀ (p : LowerPair), lowerGood p → lowerParameterBox p → let q := lowerNormalize p; lowerWidth (q.1++[2]) < lowerWidth q.2 ∧ lowerWidth (q.1++[3]) < lowerWidth q.2 ∧ lowerWidth (q.1++[1,1]) < lowerWidth q.2 ∧ lowerWidth (q.2++[1]) < lowerWidth q.1) (hwidth : LowerHistoryWidthLaw) (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t h n)
    (base : LowerPair) (p : LowerHistoryPath) (hp : lowerHistoryStructural p) (hr : lowerHistoryReached t h n base p) :
    lowerHistoryNormalizationEvents base p := by
  sorry
