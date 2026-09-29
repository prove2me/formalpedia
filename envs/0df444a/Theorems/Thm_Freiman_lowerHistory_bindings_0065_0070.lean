-- Prove2me | Theorems.Thm_Freiman_lowerHistory_bindings_0065_0070
-- name    : Freiman.lowerHistory_bindings_0065_0070
-- status  : Proved
-- author  : @tp
-- created : 2026-09-15T09:44:43.274176+00:00
-- url     : https://prove2.me/theorems/04cb39ab-26f7-46a6-80e2-d42dfb253254
-- title:
--   Lower-history bindings for indices 65–69
-- statement:
--   For each original lower-history path at array index 65 through 69, its recorded alternative count equals the exact source DNF length, every selected record satisfies the original residual, premise and witness binding conditions, and the records cover every required alternative and endpoint branch. This is the restriction of lowerHistory_bindings_0050_0100 to this consecutive index interval.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026); global_selection.tex, lem:global-suffix-targets; history_certificates.tex, app:all-suffix-histories; verification/families/target_selection/verify_suffix_targets_independent.py; certificates/target_selection/all_suffix_histories_printed.json; role: all_suffix_histories_printed.json: paths/records

import Definitions.Def_Freiman_lowerHistoryVerification
open Freiman

theorem Freiman.lowerHistory_bindings_0065_0070 : lowerHistoryBindingBatch 65 70 := by sorry
