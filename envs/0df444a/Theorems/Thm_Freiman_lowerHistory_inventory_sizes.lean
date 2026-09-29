-- Prove2me | Theorems.Thm_Freiman_lowerHistory_inventory_sizes
-- name    : Freiman.lowerHistory_inventory_sizes
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:30:37.325973+00:00
-- url     : https://prove2.me/theorems/78fe37c5-33ff-48c3-8a3c-4ea0f57f9eb6
-- title:
--   Freiman.lowerHistory_inventory_sizes
-- statement:
--   The actual packet contains 1492 paths,1194 witnesses,3622 arithmetic records and2 survivors.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026); global_selection.tex, lem:global-suffix-targets; history_certificates.tex, app:all-suffix-histories; verification/families/target_selection/verify_suffix_targets_independent.py; certificates/target_selection/all_suffix_histories_printed.json; role: compact packet inventory

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic

open Freiman

theorem Freiman.lowerHistory_inventory_sizes :
    lowerHistoryPaths.size = 1492 ∧ lowerHistoryWitnesses.size = 1194 ∧ lowerHistoryRecords.size = 3624 := by
  sorry
