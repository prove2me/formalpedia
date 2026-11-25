-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_fourier_char_smul
-- name    : GroundTheory.Automorphic.Sobolev.fourier_char_smul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:42:20.330554+00:00
-- url     : https://prove2.me/theorems/4a53a749-c50d-4844-b7c3-dc2c873914d3
-- title:
--   Sobolev: fourier char smul
-- statement:
--   The Sobolev construction uses the fourier char smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevRellich.lean#L59-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevRellich.lean#L59-L65

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevInterpolation
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidtKernel
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidtCompact
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevRellich
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

theorem GroundTheory.Automorphic.Sobolev.fourier_char_smul (χ : 𝓢(E, ℂ)) (η ξ : E) :
    𝓕 (fun x : E ↦ (𝐞 (inner ℝ x η) : ℂ) * χ x) ξ = (𝓕 χ : 𝓢(E, ℂ)) (ξ - η) := by sorry
