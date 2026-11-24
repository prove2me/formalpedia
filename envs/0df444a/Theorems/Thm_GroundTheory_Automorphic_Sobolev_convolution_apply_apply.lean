-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_convolution_apply_apply
-- name    : GroundTheory.Automorphic.Sobolev.convolution_apply_apply
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:34:41.656363+00:00
-- url     : https://prove2.me/theorems/1c4c01c0-02e7-4786-b69d-7dd38202f684
-- title:
--   Sobolev: convolution apply apply
-- statement:
--   The Sobolev construction uses the convolution apply apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMollifier.lean#L81-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMollifier.lean#L81-L83

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_Sobolev
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevDuality
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMollifier
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
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem GroundTheory.Automorphic.Sobolev.convolution_apply_apply (ψ : 𝓢(E, ℂ)) (u : 𝓢'(E, F)) (φ : 𝓢(E, ℂ)) :
    convolution F ψ u φ =
      u (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (reflect E ψ) φ) := by sorry
