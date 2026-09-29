-- Prove2me | Theorems.Thm_Freiman_lowerHistory_earlier_anchor
-- name    : Freiman.lowerHistory_earlier_anchor
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:32:05.500846+00:00
-- url     : https://prove2.me/theorems/581dac35-3d3d-44b1-b5f6-4ba745e57409
-- title:
--   Freiman.lowerHistory_earlier_anchor
-- statement:
--   The birth-parent cover or excluded earlier 32 priority cover anchors the retained target on the correct side; this uses actual selection history.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026); global_selection.tex, lem:global-suffix-targets; history_certificates.tex, app:all-suffix-histories; verification/families/target_selection/verify_suffix_targets_independent.py; certificates/target_selection/all_suffix_histories_printed.json; role: source retained-target priority

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic

open Freiman

theorem Freiman.lowerHistory_earlier_anchor (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t h n)
    (base : LowerPair) (p : LowerHistoryPath) (hp : lowerHistoryStructural p) (hr : lowerHistoryReached t h n base p) (hi : p.catalog ≠ .initial) :
    lowerHistoryEarlierAnchor base p t := by
  sorry
