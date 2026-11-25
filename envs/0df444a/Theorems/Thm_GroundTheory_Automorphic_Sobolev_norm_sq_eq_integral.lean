-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_norm_sq_eq_integral
-- name    : GroundTheory.Automorphic.Sobolev.norm_sq_eq_integral
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:47:42.310898+00:00
-- url     : https://prove2.me/theorems/9e62fe3a-8694-4568-968e-85e7de83d1ef
-- title:
--   Sobolev: norm sq eq integral
-- statement:
--   The Sobolev construction uses the norm sq eq integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/Sobolev.lean#L379-L385
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/Sobolev.lean#L379-L385

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

theorem GroundTheory.Automorphic.Sobolev.norm_sq_eq_integral {s : ℝ} (u : SobolevSpace E F s) :
    ‖u‖ ^ 2 = ∫ ξ, (1 + ‖ξ‖ ^ 2) ^ s * ‖fourierFun u ξ‖ ^ 2 := by sorry
