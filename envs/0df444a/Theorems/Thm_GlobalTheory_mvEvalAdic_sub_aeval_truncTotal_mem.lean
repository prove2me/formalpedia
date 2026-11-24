-- Prove2me | Theorems.Thm_GlobalTheory_mvEvalAdic_sub_aeval_truncTotal_mem
-- name    : GlobalTheory.mvEvalAdic_sub_aeval_truncTotal_mem
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:12:19.438749+00:00
-- url     : https://prove2.me/theorems/7ce48675-5f00-44a6-9dd8-a7b43d529d3b
-- title:
--   Global Theory: mv Eval Adic sub aeval trunc Total mem
-- statement:
--   The Global Theory construction uses the mv Eval Adic sub aeval trunc Total mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueFixedPointOfAdicContraction.lean#L60-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueFixedPointOfAdicContraction.lean#L60-L64

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PredMulSumPadicValNatFactorialAddCardLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueFixedPointOfAdicContraction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open MvPowerSeries
variable {A S σ : Type*} [CommRing A] [CommRing S] [Algebra A S]
variable [Finite σ]

theorem GlobalTheory.mvEvalAdic_sub_aeval_truncTotal_mem (J : Ideal S) [IsAdicComplete J S] (x : σ → S)
    (hx : ∀ i, x i ∈ J) (n : ℕ) (f : MvPowerSeries σ A) :
    mvEvalAdic A J x hx f - MvPolynomial.aeval x (truncTotal n f) ∈ J ^ n := by sorry
