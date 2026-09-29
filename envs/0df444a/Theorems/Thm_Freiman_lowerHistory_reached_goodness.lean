-- Prove2me | Theorems.Thm_Freiman_lowerHistory_reached_goodness
-- name    : Freiman.lowerHistory_reached_goodness
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:32:03.167988+00:00
-- url     : https://prove2.me/theorems/890f8433-a219-43d4-9c35-a4b40c52a1ef
-- title:
--   Freiman.lowerHistory_reached_goodness
-- statement:
--   Each actually visited selected pair is good; pull its necessary endpoint envelope inequalities back to the origin parameters.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026); lower_core.tex, eq:lc-natural-tails and eq:lc-full-width; global_selection.tex, lem:global-suffix-targets; verification/families/target_selection/verify_h5_original_independent.py; role: source inherited goodness

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic

open Freiman

theorem Freiman.lowerHistory_reached_goodness (hg : LowerHistoryGoodnessLaw) (hpull : LowerHistoryPullLaw) (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t h n)
    (base : LowerPair) (p : LowerHistoryPath) (hp : lowerHistoryStructural p) (hr : lowerHistoryReached t h n base p) :
    lowerHistoryGoodEvents base p := by
  sorry
