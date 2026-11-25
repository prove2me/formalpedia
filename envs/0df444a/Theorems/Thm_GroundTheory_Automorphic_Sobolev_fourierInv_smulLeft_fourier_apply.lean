-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_fourierInv_smulLeft_fourier_apply
-- name    : GroundTheory.Automorphic.Sobolev.fourierInv_smulLeft_fourier_apply
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:13:37.766379+00:00
-- url     : https://prove2.me/theorems/304ec796-7c9f-4e74-9e74-fbf890be774a
-- title:
--   Sobolev: fourier Inv smul Left fourier apply
-- statement:
--   The Sobolev construction uses the fourier Inv smul Left fourier apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevRellich.lean#L67-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevRellich.lean#L67-L82

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

theorem GroundTheory.Automorphic.Sobolev.fourierInv_smulLeft_fourier_apply (χ φ : 𝓢(E, ℂ)) (η : E) :
    (𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (χ : E → ℂ) (𝓕 φ)) : 𝓢(E, ℂ)) η =
      ∫ ξ, φ ξ * (𝓕 χ : 𝓢(E, ℂ)) (ξ - η) := by sorry
