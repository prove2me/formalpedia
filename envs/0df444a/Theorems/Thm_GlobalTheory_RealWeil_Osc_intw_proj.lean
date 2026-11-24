-- Prove2me | Theorems.Thm_GlobalTheory_RealWeil_Osc_intw_proj
-- name    : GlobalTheory.RealWeil.Osc.intw_proj
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T19:14:39.801735+00:00
-- url     : https://prove2.me/theorems/222c1bf9-91d0-4597-8021-069e419ceb0e
-- title:
--   Osc: intw proj
-- statement:
--   The Osc construction uses the intw proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsOscillatorActionOfGaussianPairings.lean#L137-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsOscillatorActionOfGaussianPairings.lean#L137-L154

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralGauTwistedConv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowMulNormGauLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionOfGaussianPairings
import Theorems.Thm_GlobalTheory_RealWeil_IsHeis_twist

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder
open GlobalTheory GlobalTheory.RealWeil GlobalTheory.RealWeil.Osc
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] {J : V ≃ₗᵢ[ℝ] V}
  {ρ ρ' : V → B →L[ℂ] B}
set_option linter.unusedSectionVars false
variable {T : B →L[ℂ] B}

theorem GlobalTheory.RealWeil.Osc.intw_proj (hJ : ∀ x, J (J x) = -x) {h : IsHeis (omJ J) ρ} (h' : IsHeis (omJ J) ρ')
    (hT : ∀ x, T (proj h x) = T x) (hT' : ∀ x, proj h' (T x) = T x) {f : B} (hf : Sm ρ f)
    (a b : V →L[ℝ] V) (hab : ∀ v, a (b v) = v) (ha : ∀ x y, omJ J (a x) (a y) = omJ J x y) :
    intw ρ' T ρ (proj (h.twist a ha) f) = proj (h'.twist a ha) (intw ρ' T ρ f) := by sorry
