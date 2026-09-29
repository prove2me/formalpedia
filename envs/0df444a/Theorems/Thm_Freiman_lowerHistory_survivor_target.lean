-- Prove2me | Theorems.Thm_Freiman_lowerHistory_survivor_target
-- name    : Freiman.lowerHistory_survivor_target
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:32:35.619387+00:00
-- url     : https://prove2.me/theorems/2794ff8a-d7e6-4b0d-9a3f-99a6c3e6adf6
-- title:
--   Freiman.lowerHistory_survivor_target
-- statement:
--   Use the corrected initial-family bridge for the two surviving paths; the discarded old eight endpoint bounds are not proof inputs.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026); initial_bridges.tex, lem:H-entry-bridges; global_selection.tex, lem:global-suffix-targets; history_certificates.tex, app:all-suffix-histories; verification/families/target_selection/verify_H_entry_reduction_independent.py; certificates/target_selection/initial_histories.json; role: corrected H-entry bridge

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic

open Freiman

theorem Freiman.lowerHistory_survivor_target (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t h n)
    (base : LowerPair) (p : LowerHistoryPath) (hp : lowerHistoryStructural p) (hr : lowerHistoryReached t h n base p) (hs : lowerHistorySurvivor p) :
    lowerHistoryTarget p.row (h n) t := by
  sorry
