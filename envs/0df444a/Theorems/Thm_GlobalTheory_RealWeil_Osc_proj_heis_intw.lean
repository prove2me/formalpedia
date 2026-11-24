-- Prove2me | Theorems.Thm_GlobalTheory_RealWeil_Osc_proj_heis_intw
-- name    : GlobalTheory.RealWeil.Osc.proj_heis_intw
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:07:24.038741+00:00
-- url     : https://prove2.me/theorems/8156a4a0-2f53-4c42-bcaa-6547bce9c490
-- title:
--   Osc: proj heis intw
-- statement:
--   The Osc construction uses the proj heis intw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsOscillatorActionOfGaussianPairings.lean#L104-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsOscillatorActionOfGaussianPairings.lean#L104-L114

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

theorem GlobalTheory.RealWeil.Osc.proj_heis_intw (hJ : ∀ x, J (J x) = -x) {h : IsHeis (omJ J) ρ} (h' : IsHeis (omJ J) ρ')
    (hT : ∀ x, T (proj h x) = T x) (hT' : ∀ x, proj h' (T x) = T x) {f : B} (hf : Good h f) (v : V) :
    proj h' (ρ' v (intw ρ' T ρ f)) = T (ρ v f) := by sorry
