-- Prove2me | Theorems.Thm_Freiman_lowerHistory_rekey_descriptor
-- name    : Freiman.lowerHistory_rekey_descriptor
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:31:45.424884+00:00
-- url     : https://prove2.me/theorems/ba201981-e829-4b20-bb53-486be77c144a
-- title:
--   Freiman.lowerHistory_rekey_descriptor
-- statement:
--   Replay and the final target row are determined by the structural key, independently of catalog ID and arithmetic fields.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026); global_selection.tex, lem:global-suffix-targets; history_certificates.tex, app:all-suffix-histories; verification/families/target_selection/verify_suffix_targets_independent.py; certificates/target_selection/all_suffix_histories_printed.json; role: descriptor bookkeeping

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic

open Freiman

theorem Freiman.lowerHistory_rekey_descriptor (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (base : LowerPair) (p p2 : LowerHistoryPath)
    (hp : lowerHistoryStructural p) (hp2 : lowerHistoryStructural p2)
    (hk : lowerHistoryPathKey p2 = lowerHistoryPathKey p) (hr : lowerHistoryReached t h n base p) :
    lowerHistoryReached t h n base p2 ∧ p2.row = p.row := by
  sorry
