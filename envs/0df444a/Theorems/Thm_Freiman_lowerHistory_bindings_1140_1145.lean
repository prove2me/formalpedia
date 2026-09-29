-- Prove2me | Theorems.Thm_Freiman_lowerHistory_bindings_1140_1145
-- name    : Freiman.lowerHistory_bindings_1140_1145
-- status  : Proved
-- author  : @tp
-- created : 2026-09-15T08:17:07.547367+00:00
-- url     : https://prove2.me/theorems/9fe36164-3496-4aec-87df-b921e6a1d303
-- title:
--   Lower-history bindings for indices 1140–1144
-- statement:
--   For each original lower-history path at array index 1140 through 1144, its recorded alternative count equals the exact source DNF length, every selected record satisfies the original residual, premise and witness binding conditions, and the records cover every required alternative and endpoint branch. This is the restriction of lowerHistory_bindings_1100_1150 to this consecutive index interval.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026); global_selection.tex, lem:global-suffix-targets; history_certificates.tex, app:all-suffix-histories; verification/families/target_selection/verify_suffix_targets_independent.py; certificates/target_selection/all_suffix_histories_printed.json; role: all_suffix_histories_printed.json: paths/records

import Definitions.Def_Freiman_lowerHistoryVerification
open Freiman

theorem Freiman.lowerHistory_bindings_1140_1145 : lowerHistoryBindingBatch 1140 1145 := by sorry
