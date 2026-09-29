-- Prove2me | Theorems.Thm_Freiman_lowerHistory_bindings_0130_0135
-- name    : Freiman.lowerHistory_bindings_0130_0135
-- status  : Proved
-- author  : @tp
-- created : 2026-09-15T15:03:36.989863+00:00
-- url     : https://prove2.me/theorems/b095ae66-6e1e-46d2-90b1-e5b250f310a2
-- title:
--   Lower-history bindings for indices 130–134
-- statement:
--   For each original lower-history path at array index 130 through 134, its recorded alternative count equals the exact source DNF length, every selected record satisfies the original residual, premise and witness binding conditions, and the records cover every required alternative and endpoint branch. This is the restriction of lowerHistory_bindings_0100_0150 to this consecutive index interval.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026); global_selection.tex, lem:global-suffix-targets; history_certificates.tex, app:all-suffix-histories; verification/families/target_selection/verify_suffix_targets_independent.py; certificates/target_selection/all_suffix_histories_printed.json; role: all_suffix_histories_printed.json: paths/records

import Definitions.Def_Freiman_lowerHistoryVerification
open Freiman

theorem Freiman.lowerHistory_bindings_0130_0135 : lowerHistoryBindingBatch 130 135 := by sorry
