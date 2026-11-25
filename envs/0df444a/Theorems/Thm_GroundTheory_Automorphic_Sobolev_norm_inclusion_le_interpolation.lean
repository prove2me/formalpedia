-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_norm_inclusion_le_interpolation
-- name    : GroundTheory.Automorphic.Sobolev.norm_inclusion_le_interpolation
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:56:27.489631+00:00
-- url     : https://prove2.me/theorems/e2e326ac-238b-4180-a9c7-d9377a10c5ce
-- title:
--   Sobolev: norm inclusion le interpolation
-- statement:
--   The Sobolev construction uses the norm inclusion le interpolation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevInterpolation.lean#L77-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevInterpolation.lean#L77-L129

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

theorem GroundTheory.Automorphic.Sobolev.norm_inclusion_le_interpolation {r t s : ℝ} (hrt : r < t) (hts : t < s)
    (v : SobolevSpace E F s) :
    ‖SobolevSpace.inclusion hts.le v‖ ≤
      ‖v‖ ^ ((t - r) / (s - r)) * ‖SobolevSpace.inclusion (hrt.trans hts).le v‖ ^ ((s - t) / (s - r)) := by sorry
