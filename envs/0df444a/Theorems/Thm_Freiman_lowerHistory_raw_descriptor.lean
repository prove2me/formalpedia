-- Prove2me | Theorems.Thm_Freiman_lowerHistory_raw_descriptor
-- name    : Freiman.lowerHistory_raw_descriptor
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:32:03.630972+00:00
-- url     : https://prove2.me/theorems/7eea25f4-8991-4cd5-ad46-95eb5eb64be9
-- title:
--   Freiman.lowerHistory_raw_descriptor
-- statement:
--   Split the actual marked history into initial and positive-time birth origins before using their separate catalogs.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026); global_selection.tex, lem:global-suffix-targets; history_certificates.tex, app:all-suffix-histories; verification/families/target_selection/verify_suffix_targets_independent.py; certificates/target_selection/all_suffix_histories_printed.json; role: source origin split

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic

open Freiman

theorem Freiman.lowerHistory_raw_descriptor (t : ℝ) (h : ℕ → LowerPair) (n row : ℕ) (hh : lowerHistory t h n)
    (hrow : row ∈ [1,2,3,4]) (haz : lowerHistoryHazard row (h n)) :
    ∃ base p, lowerHistoryStructural p ∧ lowerHistoryReached t h n base p ∧ p.row = row := by
  sorry
