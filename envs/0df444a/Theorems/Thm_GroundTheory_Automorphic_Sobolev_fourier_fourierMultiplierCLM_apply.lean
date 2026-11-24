-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_fourier_fourierMultiplierCLM_apply
-- name    : GroundTheory.Automorphic.Sobolev.fourier_fourierMultiplierCLM_apply
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:34:18.107617+00:00
-- url     : https://prove2.me/theorems/df662039-d162-4bf7-b6e3-580e836695e4
-- title:
--   Sobolev: fourier fourier Multiplier CLM apply
-- statement:
--   The Sobolev construction uses the fourier fourier Multiplier CLM apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMollifier.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMollifier.lean#L22-L24

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
variable {m : E → ℂ} {C s t : ℝ}

theorem GroundTheory.Automorphic.Sobolev.fourier_fourierMultiplierCLM_apply (m : E → ℂ) (u : 𝓢'(E, F)) (φ : 𝓢(E, ℂ)) :
    𝓕 (fourierMultiplierCLM F m u) φ = 𝓕 u (SchwartzMap.smulLeftCLM ℂ m φ) := by sorry
