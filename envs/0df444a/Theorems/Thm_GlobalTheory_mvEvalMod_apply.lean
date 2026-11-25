-- Prove2me | Theorems.Thm_GlobalTheory_mvEvalMod_apply
-- name    : GlobalTheory.mvEvalMod_apply
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:49:10.321882+00:00
-- url     : https://prove2.me/theorems/4a9cc1a6-90f7-52ab-8561-36125fbf51df
-- title:
--   Global Theory: mv Eval Mod apply
-- statement:
--   The Global Theory construction uses the mv Eval Mod apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueFixedPointOfAdicContraction.lean#L41-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueFixedPointOfAdicContraction.lean#L41-L43

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

theorem GlobalTheory.mvEvalMod_apply (J : Ideal S) (x : σ → S) (hx : ∀ i, x i ∈ J) (n : ℕ)
    (f : MvPowerSeries σ A) :
    mvEvalMod A J x hx n f = Ideal.Quotient.mk _ (MvPolynomial.aeval x (truncTotal n f)) := by sorry
