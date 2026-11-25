-- Prove2me | Theorems.Thm_GlobalTheory_continuous_sphereRotation
-- name    : GlobalTheory.continuous_sphereRotation
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:20:56.612803+00:00
-- url     : https://prove2.me/theorems/d9520be6-64aa-4495-acda-12057627366a
-- title:
--   Global Theory: continuous sphere Rotation
-- statement:
--   The Global Theory construction uses the continuous sphere Rotation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/IntegralLogNormLeHalfLogIntegralSq.lean#L22-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/IntegralLogNormLeHalfLogIntegralSq.lean#L22-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EnormPowLeInvMeasureMulLintegralBall
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegralLogNormLeHalfLogIntegralSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric Set Filter Real
open scoped ENNReal Topology Pointwise
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [MeasurableSpace E] [BorelSpace E]
omit [MeasurableSpace E] [BorelSpace E]

theorem GlobalTheory.continuous_sphereRotation :
    Continuous (Function.uncurry (sphereRotation (E := E))) := by sorry
