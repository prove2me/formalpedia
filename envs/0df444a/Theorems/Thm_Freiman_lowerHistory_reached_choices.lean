-- Prove2me | Theorems.Thm_Freiman_lowerHistory_reached_choices
-- name    : Freiman.lowerHistory_reached_choices
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:31:43.145561+00:00
-- url     : https://prove2.me/theorems/7b720614-1833-4c93-98b8-0c3bfe49e34d
-- title:
--   Freiman.lowerHistory_reached_choices
-- statement:
--   Each selected six-label source step contributes one exact DNF branch; pull it to the fixed origin orientation.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026); global_selection.tex, lem:global-suffix-targets; history_certificates.tex, app:all-suffix-histories; verification/families/target_selection/verify_suffix_targets_independent.py; certificates/target_selection/all_suffix_histories_printed.json; role: source inherited branch conditions

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic

open Freiman

theorem Freiman.lowerHistory_reached_choices (hc : LowerHistoryChoiceLaw) (hpull : LowerHistoryPullLaw) (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t h n)
    (base : LowerPair) (p : LowerHistoryPath) (hp : lowerHistoryStructural p) (hr : lowerHistoryReached t h n base p) :
    lowerHistoryChoiceEvents base p := by
  sorry
