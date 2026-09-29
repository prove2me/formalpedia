-- Prove2me | Theorems.Thm_Freiman_lowerHistory_bindings_0140_0145
-- name    : Freiman.lowerHistory_bindings_0140_0145
-- status  : Proved
-- author  : @tp
-- created : 2026-09-15T15:03:46.685806+00:00
-- url     : https://prove2.me/theorems/65650057-f5a3-41f1-8945-2b209bcfe1b8
-- title:
--   Lower-history bindings for indices 140–144
-- statement:
--   For each original lower-history path at array index 140 through 144, its recorded alternative count equals the exact source DNF length, every selected record satisfies the original residual, premise and witness binding conditions, and the records cover every required alternative and endpoint branch. This is the restriction of lowerHistory_bindings_0100_0150 to this consecutive index interval.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026); global_selection.tex, lem:global-suffix-targets; history_certificates.tex, app:all-suffix-histories; verification/families/target_selection/verify_suffix_targets_independent.py; certificates/target_selection/all_suffix_histories_printed.json; role: all_suffix_histories_printed.json: paths/records

import Definitions.Def_Freiman_lowerHistoryVerification
open Freiman

theorem Freiman.lowerHistory_bindings_0140_0145 : lowerHistoryBindingBatch 140 145 := by sorry
