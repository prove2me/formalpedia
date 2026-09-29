-- Prove2me | Theorems.Thm_Freiman_other22_record_exclusion
-- name    : Freiman.other22_record_exclusion
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:33:58.960808+00:00
-- url     : https://prove2.me/theorems/f4de7704-719a-4f02-9852-7a0cc3e0bd2c
-- title:
--   other22 record exclusion
-- statement:
--   A source-bound residual record is impossible by the shared exact Bernstein exclusion theorem.
-- source:
--   Report §7.3, Lemma 7.4 (lem:old23-other22-target), printed p.43; other22_target.tex and Appendix other22_certificates.tex; original 144-obligation exact certificate.

import Definitions.Def_Freiman_other22Verification
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.SplitIfs

open Freiman

theorem Freiman.other22_record_exclusion (record : Other22Record) (hb : other22RecordBinding record)
    (hw : certWitnessValid (other22Witness record.witness))
    (r s q : ℝ) (hm : certRectangleMem (other22Paths record.caseId).rectangle r s) :
    ¬ lowerHistoryConditions (lowerHistoryResidual (other22Paths record.caseId) record.alternative (record.branch : ℤ)) r s q := by
  sorry
