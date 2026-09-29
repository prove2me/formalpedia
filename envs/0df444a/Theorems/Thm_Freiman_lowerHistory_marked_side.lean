-- Prove2me | Theorems.Thm_Freiman_lowerHistory_marked_side
-- name    : Freiman.lowerHistory_marked_side
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:31:52.723884+00:00
-- url     : https://prove2.me/theorems/1888f718-0d11-4bb3-81cd-616dc7727662
-- title:
--   Freiman.lowerHistory_marked_side
-- statement:
--   Convert the normalized left/right hazard to its permanent physical marked side, retaining incoming order at ties.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026); global_selection.tex, lem:global-suffix-targets; history_certificates.tex, app:all-suffix-histories; verification/families/target_selection/verify_suffix_targets_independent.py; certificates/target_selection/all_suffix_histories_printed.json; role: source physical-side invariant

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic

open Freiman

theorem Freiman.lowerHistory_marked_side (h : ℕ → LowerPair) (n row : ℕ) (hrow : row ∈ [1,2,3,4]) (haz : lowerHistoryHazard row (h n)) :
    lowerEnds (lowerSide (lowerPhysicalPath h n) (lowerMarkedPhysical h n row)) [3,1,3,1] := by
  sorry
