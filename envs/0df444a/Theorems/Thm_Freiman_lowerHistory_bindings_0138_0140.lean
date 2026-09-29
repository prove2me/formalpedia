-- Prove2me | Theorems.Thm_Freiman_lowerHistory_bindings_0138_0140
-- name    : Freiman.lowerHistory_bindings_0138_0140
-- status  : Proved
-- author  : @tp
-- created : 2026-09-15T15:48:43.40485+00:00
-- url     : https://prove2.me/theorems/d49b8b59-d061-44f6-9a72-6c644f17a21e
-- title:
--   Lower-history bindings for indices 138–139
-- statement:
--   For each original lower-history path at array index 138 through 139, its recorded alternative count equals the exact source DNF length, every selected record satisfies the original residual, premise and witness binding conditions, and the records cover every required alternative and endpoint branch. This is the restriction of lowerHistory_bindings_0100_0150 to this consecutive index interval.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026); global_selection.tex, lem:global-suffix-targets; history_certificates.tex, app:all-suffix-histories; verification/families/target_selection/verify_suffix_targets_independent.py; certificates/target_selection/all_suffix_histories_printed.json; role: all_suffix_histories_printed.json: paths/records

import Definitions.Def_Freiman_lowerHistoryVerification
open Freiman

theorem Freiman.lowerHistory_bindings_0138_0140 : lowerHistoryBindingBatch 138 140 := by sorry
