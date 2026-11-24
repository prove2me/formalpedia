-- Prove2me | Theorems.Thm_GlobalTheory_RealWeil_Osc_intw_comm
-- name    : GlobalTheory.RealWeil.Osc.intw_comm
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T19:14:45.418461+00:00
-- url     : https://prove2.me/theorems/6895fe93-0340-49ee-8af0-a936dbca7d1f
-- title:
--   Osc: intw comm
-- statement:
--   The Osc construction uses the intw comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsOscillatorActionOfGaussianPairings.lean#L169-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsOscillatorActionOfGaussianPairings.lean#L169-L174

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

theorem GlobalTheory.RealWeil.Osc.intw_comm {h : IsHeis (omJ J) ρ} (h' : IsHeis (omJ J) ρ') (hT : ∀ x, T (proj h x) = T x)
    {f : B} (hf : Good h f) (A : B →L[ℂ] B) (hA : ∀ v f, A (ρ v f) = ρ v (A f))
    (hA' : ∀ v f, A (ρ' v f) = ρ' v (A f)) (hAT : ∀ x, A (T x) = T (A x)) :
    intw ρ' T ρ (A f) = A (intw ρ' T ρ f) := by sorry
