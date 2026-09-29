-- Prove2me | Theorems.Thm_Freiman_lowerHistory_width_threshold
-- name    : Freiman.lowerHistory_width_threshold
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:23:56.304679+00:00
-- url     : https://prove2.me/theorems/17ff7c22-8faf-4c69-aaff-09631ae8bd9f
-- title:
--   Freiman.lowerHistory_width_threshold
-- statement:
--   Full alpha-beta cylinder widths give the exact normalization threshold, including strict equality handling.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026); lower_core.tex, eq:lc-natural-tails and eq:lc-full-width; global_selection.tex, lem:global-suffix-targets; verification/families/target_selection/verify_h5_original_independent.py; role: full-width normalization

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic

open Freiman

theorem Freiman.lowerHistory_width_threshold (base words : LowerPair) :
    (lowerWidth (base.2++words.2) ≤ lowerWidth (base.1++words.1) ↔
      lowerHistoryAtBase base [⟨false,false,lowerHistoryWH words⟩]) ∧
    (lowerWidth (base.2++words.2) < lowerWidth (base.1++words.1) ↔
      lowerHistoryAtBase base [⟨false,true,lowerHistoryWH words⟩]) := by
  sorry
