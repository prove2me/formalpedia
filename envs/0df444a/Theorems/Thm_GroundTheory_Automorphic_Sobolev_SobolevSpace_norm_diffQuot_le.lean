-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_norm_diffQuot_le
-- name    : GroundTheory.Automorphic.Sobolev.SobolevSpace.norm_diffQuot_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:55:50.713925+00:00
-- url     : https://prove2.me/theorems/28b991b3-747b-4d36-93fa-d1c31b2fd4c4
-- title:
--   Sobolev Space: norm diff Quot le
-- statement:
--   The Sobolev Space construction uses the norm diff Quot le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevFriedrichs.lean#L280-L287
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevFriedrichs.lean#L280-L287

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMollifier
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevFriedrichs
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
open GroundTheory.Automorphic.Sobolev.SobolevSpace
variable {s : ℝ}

theorem GroundTheory.Automorphic.Sobolev.SobolevSpace.norm_diffQuot_le (v : E) (t : ℝ) (u : SobolevSpace E F (s + 1)) :
    ‖diffQuot v t (inclusion (le_add_of_nonneg_right zero_le_one) u)‖ ≤ 2 * Real.pi * ‖v‖ * ‖u‖ := by sorry
