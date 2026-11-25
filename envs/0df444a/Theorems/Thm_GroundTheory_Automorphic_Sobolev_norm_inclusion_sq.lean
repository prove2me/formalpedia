-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_norm_inclusion_sq
-- name    : GroundTheory.Automorphic.Sobolev.norm_inclusion_sq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:56:55.352589+00:00
-- url     : https://prove2.me/theorems/6d0d821b-b110-4bb5-867b-e3767fc34ef9
-- title:
--   Sobolev: norm inclusion sq
-- statement:
--   The Sobolev construction uses the norm inclusion sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevInterpolation.lean#L55-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevInterpolation.lean#L55-L60

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

theorem GroundTheory.Automorphic.Sobolev.norm_inclusion_sq {s t : ℝ} (h : t ≤ s) (v : SobolevSpace E F s) :
    ‖SobolevSpace.inclusion h v‖ ^ 2 = ∫ ξ, (1 + ‖ξ‖ ^ 2) ^ t * ‖fourierFun v ξ‖ ^ 2 := by sorry
