-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_fourier_fourierMultiplierCLM_weight_apply
-- name    : GroundTheory.Automorphic.Sobolev.fourier_fourierMultiplierCLM_weight_apply
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:51:53.441821+00:00
-- url     : https://prove2.me/theorems/46a063e0-6937-41b3-819c-3acf039b184d
-- title:
--   Sobolev: fourier fourier Multiplier CLM weight apply
-- statement:
--   The Sobolev construction uses the fourier fourier Multiplier CLM weight apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMultiplication.lean#L106-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMultiplication.lean#L106-L110

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

theorem GroundTheory.Automorphic.Sobolev.fourier_fourierMultiplierCLM_weight_apply (r : ℝ) (φ : 𝓢(E, ℂ)) (ξ : E) :
    (𝓕 (SchwartzMap.fourierMultiplierCLM ℂ (weight r) φ) : 𝓢(E, ℂ)) ξ =
      weight r ξ * (𝓕 φ : 𝓢(E, ℂ)) ξ := by sorry
