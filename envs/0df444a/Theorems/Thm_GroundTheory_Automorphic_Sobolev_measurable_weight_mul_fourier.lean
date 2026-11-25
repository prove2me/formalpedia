-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_measurable_weight_mul_fourier
-- name    : GroundTheory.Automorphic.Sobolev.measurable_weight_mul_fourier
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T01:49:56.367895+00:00
-- url     : https://prove2.me/theorems/3b4b70fa-15cf-5d6b-b825-d78143cacd96
-- title:
--   Sobolev: measurable weight mul fourier
-- statement:
--   The Sobolev construction uses the measurable weight mul fourier property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMultiplication.lean#L225-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMultiplication.lean#L225-L227

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

theorem GroundTheory.Automorphic.Sobolev.measurable_weight_mul_fourier (r : ℝ) (φ : 𝓢(E, ℂ)) :
    Measurable fun ξ ↦ weight r ξ * (𝓕 φ : 𝓢(E, ℂ)) ξ := by sorry
