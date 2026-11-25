-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_fourierFun_inclusion
-- name    : GroundTheory.Automorphic.Sobolev.fourierFun_inclusion
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:53:08.075205+00:00
-- url     : https://prove2.me/theorems/64f82e30-fbd6-4fe8-8aec-748ddb633631
-- title:
--   Sobolev: fourier Fun inclusion
-- statement:
--   The Sobolev construction uses the fourier Fun inclusion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevInterpolation.lean#L47-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevInterpolation.lean#L47-L53

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevFriedrichs
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevInterpolation
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

theorem GroundTheory.Automorphic.Sobolev.fourierFun_inclusion {s t : ℝ} (h : t ≤ s) (v : SobolevSpace E F s) :
    fourierFun (SobolevSpace.inclusion h v) =ᵐ[volume] fourierFun v := by sorry
