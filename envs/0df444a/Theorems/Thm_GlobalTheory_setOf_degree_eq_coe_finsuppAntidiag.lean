-- Prove2me | Theorems.Thm_GlobalTheory_setOf_degree_eq_coe_finsuppAntidiag
-- name    : GlobalTheory.setOf_degree_eq_coe_finsuppAntidiag
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:20:07.045812+00:00
-- url     : https://prove2.me/theorems/72383eed-ed35-4b7e-a867-2cc3dc134e26
-- title:
--   Global Theory: set Of degree eq coe finsupp Antidiag
-- statement:
--   The Global Theory construction uses the set Of degree eq coe finsupp Antidiag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MonomialCountAndBinomialEstimates.lean#L7-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MonomialCountAndBinomialEstimates.lean#L7-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MonomialCountAndBinomialEstimates
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Finset

theorem GlobalTheory.setOf_degree_eq_coe_finsuppAntidiag (σ : Type*) [Fintype σ] [DecidableEq σ] (a : ℕ) :
    {α : σ →₀ ℕ | α.degree = a} = ↑(finsuppAntidiag (univ : Finset σ) a) := by sorry
