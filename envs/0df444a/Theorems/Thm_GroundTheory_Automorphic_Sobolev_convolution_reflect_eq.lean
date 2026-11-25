-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_convolution_reflect_eq
-- name    : GroundTheory.Automorphic.Sobolev.convolution_reflect_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:33:55.557332+00:00
-- url     : https://prove2.me/theorems/95506828-b0e4-4e80-bcce-6c09bbf8c54c
-- title:
--   Sobolev: convolution reflect eq
-- statement:
--   The Sobolev construction uses the convolution reflect eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMollifier.lean#L89-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMollifier.lean#L89-L104

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

theorem GroundTheory.Automorphic.Sobolev.convolution_reflect_eq (ψ φ : 𝓢(E, ℂ)) :
    SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (reflect E ψ) φ =
      𝓕 (SchwartzMap.smulLeftCLM ℂ ⇑(𝓕 ψ : 𝓢(E, ℂ)) (𝓕⁻ φ)) := by sorry
