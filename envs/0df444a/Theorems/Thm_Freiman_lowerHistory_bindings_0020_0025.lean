-- Prove2me | Theorems.Thm_Freiman_lowerHistory_bindings_0020_0025
-- name    : Freiman.lowerHistory_bindings_0020_0025
-- status  : Proved
-- author  : @tp
-- created : 2026-09-15T17:49:55.491546+00:00
-- url     : https://prove2.me/theorems/e30427bb-f931-4073-8b95-e8a33df8c755
-- title:
--   Lower-history bindings for indices 20–24
-- statement:
--   For each original lower-history path at array index 20 through 24, its recorded alternative count equals the exact source DNF length, every selected record satisfies the original residual, premise and witness binding conditions, and the records cover every required alternative and endpoint branch. This is the restriction of lowerHistory_bindings_0000_0050 to this consecutive index interval.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026); global_selection.tex, lem:global-suffix-targets; history_certificates.tex, app:all-suffix-histories; verification/families/target_selection/verify_suffix_targets_independent.py; certificates/target_selection/all_suffix_histories_printed.json; role: all_suffix_histories_printed.json: paths/records

import Definitions.Def_Freiman_lowerHistoryVerification
open Freiman

theorem Freiman.lowerHistory_bindings_0020_0025 : lowerHistoryBindingBatch 20 25 := by sorry
