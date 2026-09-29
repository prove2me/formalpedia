-- Prove2me | Theorems.Thm_Freiman_lowerHistory_bindings_0100_0105
-- name    : Freiman.lowerHistory_bindings_0100_0105
-- status  : Proved
-- author  : @tp
-- created : 2026-09-15T15:03:39.206804+00:00
-- url     : https://prove2.me/theorems/87f509d6-158a-4e2a-9ea7-8fb34e0a345a
-- title:
--   Lower-history bindings for indices 100–104
-- statement:
--   For each original lower-history path at array index 100 through 104, its recorded alternative count equals the exact source DNF length, every selected record satisfies the original residual, premise and witness binding conditions, and the records cover every required alternative and endpoint branch. This is the restriction of lowerHistory_bindings_0100_0150 to this consecutive index interval.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026); global_selection.tex, lem:global-suffix-targets; history_certificates.tex, app:all-suffix-histories; verification/families/target_selection/verify_suffix_targets_independent.py; certificates/target_selection/all_suffix_histories_printed.json; role: all_suffix_histories_printed.json: paths/records

import Definitions.Def_Freiman_lowerHistoryVerification
open Freiman

theorem Freiman.lowerHistory_bindings_0100_0105 : lowerHistoryBindingBatch 100 105 := by sorry
