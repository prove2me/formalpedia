-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_weight_mul_fourier_commRem
-- name    : GroundTheory.Automorphic.Sobolev.weight_mul_fourier_commRem
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:14:45.127119+00:00
-- url     : https://prove2.me/theorems/d2262ae3-6a8d-457d-8cf7-c29f896a76da
-- title:
--   Sobolev: weight mul fourier comm Rem
-- statement:
--   The Sobolev construction uses the weight mul fourier comm Rem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMultiplication.lean#L268-L294
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMultiplication.lean#L268-L294

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevRellich
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevEmbedding
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable (χ : 𝓢(E, ℂ))

theorem GroundTheory.Automorphic.Sobolev.weight_mul_fourier_commRem (r : ℝ) (φ : 𝓢(E, ℂ)) (ξ : E) :
    weight r ξ * (𝓕 (commRem χ r φ) : 𝓢(E, ℂ)) ξ =
      ∫ η, (𝓕 χ : 𝓢(E, ℂ)) (ξ - η) * ((weight r ξ - weight r η) * (𝓕 φ : 𝓢(E, ℂ)) η) := by sorry
