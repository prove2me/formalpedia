-- Prove2me | Theorems.Thm_GlobalTheory_eq_mvEvalAdic
-- name    : GlobalTheory.eq_mvEvalAdic
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:17:28.982815+00:00
-- url     : https://prove2.me/theorems/adf28d42-97b7-43ad-bb8a-55352d0bc06a
-- title:
--   Global Theory: eq mv Eval Adic
-- statement:
--   The Global Theory construction uses the eq mv Eval Adic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueFixedPointOfAdicContraction.lean#L143-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueFixedPointOfAdicContraction.lean#L143-L145

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

theorem GlobalTheory.eq_mvEvalAdic (J : Ideal S) [IsAdicComplete J S] (x : σ → S) (hx : ∀ i, x i ∈ J)
    (φ : MvPowerSeries σ A →ₐ[A] S) (h : ∀ i, φ (X i) = x i) : φ = mvEvalAdic A J x hx := by sorry
