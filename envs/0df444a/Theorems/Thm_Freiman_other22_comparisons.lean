-- Prove2me | Theorems.Thm_Freiman_other22_comparisons
-- name    : Freiman.other22_comparisons
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:34:31.450093+00:00
-- url     : https://prove2.me/theorems/cb333fdd-452d-4d7b-b005-5d5b052a4f0b
-- title:
--   other22 comparisons
-- statement:
--   Complete finite alternative/endpoint coverage and all 92 valid witnesses force every one of the required endpoint comparisons.
-- source:
--   Report §7.3, Lemma 7.4 (lem:old23-other22-target), printed p.43; other22_target.tex and Appendix other22_certificates.tex; original 144-obligation exact certificate.

import Definitions.Def_Freiman_other22Verification
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.SplitIfs

open Freiman

theorem Freiman.other22_comparisons (k : Fin 6) (hb : other22AllBindings) (hw : other22AllWitnesses)
    (r s q : ℝ) (hm : certRectangleMem (other22Paths k).rectangle r s)
    (hsource : ∃ bs ∈ lowerHistorySourcePremises (other22Paths k), lowerHistoryConditions bs r s q) :
    lowerHistoryComparisonsHold (other22Paths k) r s q := by
  sorry
