-- Prove2me | Theorems.Thm_Freiman_lowerHistory_bindings_0085_0090
-- name    : Freiman.lowerHistory_bindings_0085_0090
-- status  : Proved
-- author  : @tp
-- created : 2026-09-15T09:45:16.995738+00:00
-- url     : https://prove2.me/theorems/c2444785-b35c-490c-bbd7-53c102e3c928
-- title:
--   Lower-history bindings for indices 85–89
-- statement:
--   For each original lower-history path at array index 85 through 89, its recorded alternative count equals the exact source DNF length, every selected record satisfies the original residual, premise and witness binding conditions, and the records cover every required alternative and endpoint branch. This is the restriction of lowerHistory_bindings_0050_0100 to this consecutive index interval.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026); global_selection.tex, lem:global-suffix-targets; history_certificates.tex, app:all-suffix-histories; verification/families/target_selection/verify_suffix_targets_independent.py; certificates/target_selection/all_suffix_histories_printed.json; role: all_suffix_histories_printed.json: paths/records

import Definitions.Def_Freiman_lowerHistoryVerification
open Freiman

theorem Freiman.lowerHistory_bindings_0085_0090 : lowerHistoryBindingBatch 85 90 := by sorry
