-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_norm_sq_eq_integral_of_fourier
-- name    : GroundTheory.Automorphic.Sobolev.norm_sq_eq_integral_of_fourier
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:33:32.017123+00:00
-- url     : https://prove2.me/theorems/fa22faab-42ee-4be1-a177-05153765be03
-- title:
--   Sobolev: norm sq eq integral of fourier
-- statement:
--   The Sobolev construction uses the norm sq eq integral of fourier property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/Sobolev.lean#L409-L437
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/Sobolev.lean#L409-L437

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_Sobolev
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

theorem GroundTheory.Automorphic.Sobolev.norm_sq_eq_integral_of_fourier {s : ℝ} (u : SobolevSpace E F s) (g : E → F)
    (hg : MemLp (fun ξ ↦ weight s ξ • g ξ) 2 (volume : Measure E))
    (hφ : ∀ φ : 𝓢(E, ℂ), 𝓕 (SobolevSpace.toDistribution u) φ = ∫ ξ, φ ξ • g ξ) :
    g =ᵐ[volume] fourierFun u ∧ ‖u‖ ^ 2 = ∫ ξ, (1 + ‖ξ‖ ^ 2) ^ s * ‖g ξ‖ ^ 2 := by sorry
