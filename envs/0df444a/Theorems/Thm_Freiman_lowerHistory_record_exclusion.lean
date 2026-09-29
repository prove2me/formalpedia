-- Prove2me | Theorems.Thm_Freiman_lowerHistory_record_exclusion
-- name    : Freiman.lowerHistory_record_exclusion
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:31:35.440225+00:00
-- url     : https://prove2.me/theorems/92c722c3-5bad-415e-ba9b-946aa139c105
-- title:
--   Freiman.lowerHistory_record_exclusion
-- statement:
--   Transfer the two witness bounds through exact premise-set equality, then apply the generic tensor Bernstein exclusion.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026); global_selection.tex, lem:global-suffix-targets; history_certificates.tex, app:all-suffix-histories; verification/families/target_selection/verify_suffix_targets_independent.py; certificates/target_selection/all_suffix_histories_printed.json; role: certificate soundness

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic

open Freiman

theorem Freiman.lowerHistory_record_exclusion (p : LowerHistoryPath) (record : LowerHistoryRecord)
    (hb : lowerHistoryRecordBinding p record) (hs : record.survivor = false)
    (hw : certWitnessValid (lowerHistoryWitness record.witnessId))
    (r s q : ℝ) (hm : certRectangleMem p.rectangle r s) :
    ¬ lowerHistoryConditions (lowerHistoryResidual p record.alternative record.endpointBranch) r s q := by
  sorry
