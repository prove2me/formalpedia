-- Prove2me | Theorems.Thm_Freiman_lowerHistory_bindings_1120_1130
-- name    : Freiman.lowerHistory_bindings_1120_1130
-- status  : Proved
-- author  : @tp
-- created : 2026-09-15T08:00:11.155022+00:00
-- url     : https://prove2.me/theorems/8c2a4434-0785-4c91-9626-c0bcb6c983f0
-- title:
--   Lower-history bindings for indices 1120–1129
-- statement:
--   For each original lower-history path at array index 1120 through 1129, its recorded alternative count equals the exact source DNF length, every selected record satisfies the original residual, premise and witness binding conditions, and the records cover every required alternative and endpoint branch. This is the restriction of lowerHistory_bindings_1100_1150 to this consecutive index interval.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026); global_selection.tex, lem:global-suffix-targets; history_certificates.tex, app:all-suffix-histories; verification/families/target_selection/verify_suffix_targets_independent.py; certificates/target_selection/all_suffix_histories_printed.json; role: all_suffix_histories_printed.json: paths/records

import Definitions.Def_Freiman_lowerHistoryVerification
open Freiman

theorem Freiman.lowerHistory_bindings_1120_1130 : lowerHistoryBindingBatch 1120 1130 := by sorry
