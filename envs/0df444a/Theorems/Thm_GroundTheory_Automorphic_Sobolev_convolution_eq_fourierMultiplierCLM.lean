-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_convolution_eq_fourierMultiplierCLM
-- name    : GroundTheory.Automorphic.Sobolev.convolution_eq_fourierMultiplierCLM
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:34:07.915937+00:00
-- url     : https://prove2.me/theorems/eca5a6eb-0323-48d1-8383-65b13bf33ac8
-- title:
--   Sobolev: convolution eq fourier Multiplier CLM
-- statement:
--   The Sobolev construction uses the convolution eq fourier Multiplier CLM property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMollifier.lean#L106-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMollifier.lean#L106-L109

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

theorem GroundTheory.Automorphic.Sobolev.convolution_eq_fourierMultiplierCLM (ψ : 𝓢(E, ℂ)) (u : 𝓢'(E, F)) :
    convolution F ψ u = fourierMultiplierCLM F ⇑(𝓕 ψ : 𝓢(E, ℂ)) u := by sorry
