-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_fourier_bessel_inclusion_eq
-- name    : GroundTheory.Automorphic.Sobolev.fourier_bessel_inclusion_eq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:13:32.314394+00:00
-- url     : https://prove2.me/theorems/c4372030-a521-4696-8d8e-2eba35249c22
-- title:
--   Sobolev: fourier bessel inclusion eq
-- statement:
--   The Sobolev construction uses the fourier bessel inclusion eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevRellich.lean#L201-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevRellich.lean#L201-L253

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
variable {s N : ℝ} (χ : 𝓢(E, ℂ))

theorem GroundTheory.Automorphic.Sobolev.fourier_bessel_inclusion_eq (hN : (Module.finrank ℝ E : ℝ) < 2 * N)
    (u : SobolevSpace E ℂ s)
    (hu : smulLeftCLM ℂ (χ : E → ℂ) (SobolevSpace.toDistribution u) = SobolevSpace.toDistribution u) :
    (𝓕 (SobolevSpace.bessel (s - N) (SobolevSpace.inclusion (by linarith : s - N ≤ s) u)) :
      Lp ℂ 2 (volume : Measure E)) = rellichOp (s := s) χ hN (𝓕 (SobolevSpace.bessel s u)) := by sorry
