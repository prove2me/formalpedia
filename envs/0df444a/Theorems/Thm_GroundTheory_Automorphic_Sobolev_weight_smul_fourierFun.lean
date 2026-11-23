-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_weight_smul_fourierFun
-- name    : GroundTheory.Automorphic.Sobolev.weight_smul_fourierFun
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:47:06.115618+00:00
-- url     : https://prove2.me/theorems/2e4a8a7a-43a4-4aa3-815f-89d074fd7c67
-- title:
--   Sobolev: weight smul fourier Fun
-- statement:
--   The Sobolev construction uses the weight smul fourier Fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/Sobolev.lean#L375-L377
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/Sobolev.lean#L375-L377

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

theorem GroundTheory.Automorphic.Sobolev.weight_smul_fourierFun {s : ℝ} (u : SobolevSpace E F s) (ξ : E) :
    weight s ξ • fourierFun u ξ = (𝓕 (SobolevSpace.bessel s u) : Lp F 2 (volume : Measure E)) ξ := by sorry
