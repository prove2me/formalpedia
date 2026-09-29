-- Prove2me | Theorems.Thm_Freiman_lowerHistory_bindings_0137_0138
-- name    : Freiman.lowerHistory_bindings_0137_0138
-- status  : Proved
-- author  : @tp
-- created : 2026-09-15T15:48:47.110223+00:00
-- url     : https://prove2.me/theorems/e3684842-63dd-4cb6-963c-9c471c9ad072
-- title:
--   Lower-history bindings for indices 137–137
-- statement:
--   For each original lower-history path at array index 137 through 137, its recorded alternative count equals the exact source DNF length, every selected record satisfies the original residual, premise and witness binding conditions, and the records cover every required alternative and endpoint branch. This is the restriction of lowerHistory_bindings_0100_0150 to this consecutive index interval.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026); global_selection.tex, lem:global-suffix-targets; history_certificates.tex, app:all-suffix-histories; verification/families/target_selection/verify_suffix_targets_independent.py; certificates/target_selection/all_suffix_histories_printed.json; role: all_suffix_histories_printed.json: paths/records

import Definitions.Def_Freiman_lowerHistoryVerification
open Freiman

theorem Freiman.lowerHistory_bindings_0137_0138 : lowerHistoryBindingBatch 137 138 := by sorry
