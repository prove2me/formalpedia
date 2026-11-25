-- Prove2me | Theorems.Thm_GlobalTheory_measurePreserving_sphereRotation
-- name    : GlobalTheory.measurePreserving_sphereRotation
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T02:55:21.48044+00:00
-- url     : https://prove2.me/theorems/baae14d3-10d3-45a9-b7d0-cdd1cd49cb19
-- title:
--   Global Theory: measure Preserving sphere Rotation
-- statement:
--   The Global Theory construction uses the measure Preserving sphere Rotation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/IntegralLogNormLeHalfLogIntegralSq.lean#L35-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/IntegralLogNormLeHalfLogIntegralSq.lean#L35-L73

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
variable [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

theorem GlobalTheory.measurePreserving_sphereRotation [FiniteDimensional ℂ E] (μ : Measure E)
    [μ.IsAddHaarMeasure] (θ : ℝ) :
    MeasurePreserving (sphereRotation θ) μ.toSphere μ.toSphere := by sorry
