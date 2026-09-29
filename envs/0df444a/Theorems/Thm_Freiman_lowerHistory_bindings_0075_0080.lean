-- Prove2me | Theorems.Thm_Freiman_lowerHistory_bindings_0075_0080
-- name    : Freiman.lowerHistory_bindings_0075_0080
-- status  : Proved
-- author  : @tp
-- created : 2026-09-15T09:44:49.076705+00:00
-- url     : https://prove2.me/theorems/82676b00-8247-4724-af01-f612f0afc59c
-- title:
--   Lower-history bindings for indices 75–79
-- statement:
--   For each original lower-history path at array index 75 through 79, its recorded alternative count equals the exact source DNF length, every selected record satisfies the original residual, premise and witness binding conditions, and the records cover every required alternative and endpoint branch. This is the restriction of lowerHistory_bindings_0050_0100 to this consecutive index interval.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026); global_selection.tex, lem:global-suffix-targets; history_certificates.tex, app:all-suffix-histories; verification/families/target_selection/verify_suffix_targets_independent.py; certificates/target_selection/all_suffix_histories_printed.json; role: all_suffix_histories_printed.json: paths/records

import Definitions.Def_Freiman_lowerHistoryVerification
open Freiman

theorem Freiman.lowerHistory_bindings_0075_0080 : lowerHistoryBindingBatch 75 80 := by sorry
