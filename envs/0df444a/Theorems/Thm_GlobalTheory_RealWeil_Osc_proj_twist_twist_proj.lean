-- Prove2me | Theorems.Thm_GlobalTheory_RealWeil_Osc_proj_twist_twist_proj
-- name    : GlobalTheory.RealWeil.Osc.proj_twist_twist_proj
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T19:16:43.899837+00:00
-- url     : https://prove2.me/theorems/1452489a-65bc-42bb-a6f6-480982c6bcd7
-- title:
--   Osc: proj twist twist proj
-- statement:
--   The Osc construction uses the proj twist twist proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsOscillatorActionOfGaussianPairings.lean#L181-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsOscillatorActionOfGaussianPairings.lean#L181-L193

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

theorem GlobalTheory.RealWeil.Osc.proj_twist_twist_proj (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) (a b : V →L[ℝ] V)
    (ha : ∀ x y, omJ J (a x) (a y) = omJ J x y) (hb : ∀ x y, omJ J (b x) (b y) = omJ J x y) (x : B) :
    proj h (proj (h.twist a ha) (proj (h.twist b hb) (proj h x))) = mu J a b • proj h x := by sorry
