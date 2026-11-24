-- Prove2me | Theorems.Thm_GlobalTheory_RealWeil_Osc_inner_intw
-- name    : GlobalTheory.RealWeil.Osc.inner_intw
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T19:14:44.087732+00:00
-- url     : https://prove2.me/theorems/7b922e4d-eb8f-4040-8fcb-09f1d6635dd2
-- title:
--   Osc: inner intw
-- statement:
--   The Osc construction uses the inner intw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsOscillatorActionOfGaussianPairings.lean#L223-L230
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsOscillatorActionOfGaussianPairings.lean#L223-L230

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralGauTwistedConv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowMulNormGauLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionOfGaussianPairings
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
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Φ : B →L[ℂ] H}

theorem GlobalTheory.RealWeil.Osc.inner_intw (hJ : ∀ x, J (J x) = -x) {h : IsHeis (omJ J) ρ} (h' : IsHeis (omJ J) ρ')
    (hΦ : ∀ v f, ‖Φ (ρ' v f)‖ = ‖Φ f‖)
    (hT : ∀ x, T (proj h x) = T x) (hT' : ∀ x, proj h' (T x) = T x) {f : B} (hf : Good h f) :
    inner ℂ (Φ (intw ρ' T ρ f)) (Φ (intw ρ' T ρ f)) = ∫ w, inner ℂ (Φ (T (ρ (-w) f))) (Φ (T (ρ (-w) f))) := by sorry
