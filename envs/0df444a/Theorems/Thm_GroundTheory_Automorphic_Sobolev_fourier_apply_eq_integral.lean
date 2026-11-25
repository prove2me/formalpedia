-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_fourier_apply_eq_integral
-- name    : GroundTheory.Automorphic.Sobolev.fourier_apply_eq_integral
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:47:20.342169+00:00
-- url     : https://prove2.me/theorems/99c4531b-eb67-4df1-bb99-d1e1656ac3d6
-- title:
--   Sobolev: fourier apply eq integral
-- statement:
--   The Sobolev construction uses the fourier apply eq integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/Sobolev.lean#L359-L368
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/Sobolev.lean#L359-L368

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

theorem GroundTheory.Automorphic.Sobolev.fourier_apply_eq_integral {s : ℝ} (u : SobolevSpace E F s) (φ : 𝓢(E, ℂ)) :
    𝓕 (SobolevSpace.toDistribution u) φ = ∫ ξ, φ ξ • fourierFun u ξ := by sorry
