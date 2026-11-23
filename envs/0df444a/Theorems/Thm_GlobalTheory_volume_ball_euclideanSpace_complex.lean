-- Prove2me | Theorems.Thm_GlobalTheory_volume_ball_euclideanSpace_complex
-- name    : GlobalTheory.volume_ball_euclideanSpace_complex
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:17:16.484805+00:00
-- url     : https://prove2.me/theorems/3011ce67-bc2b-4d9e-bb44-caf24bd3df88
-- title:
--   Global Theory: volume ball euclidean Space complex
-- statement:
--   The Global Theory construction uses the volume ball euclidean Space complex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EnormPowLeInvMeasureMulLintegralBall.lean#L275-L280
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EnormPowLeInvMeasureMulLintegralBall.lean#L275-L280

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EnormPowLeInvMeasureMulLintegralBall
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric Set
open scoped ENNReal Real
open GlobalTheory
variable {ι : Type*} [Fintype ι]

theorem GlobalTheory.volume_ball_euclideanSpace_complex (a : EuclideanSpace ℂ ι) {r : ℝ} (hr : 0 < r) :
    volume (ball a r) = ENNReal.ofReal (π ^ Fintype.card ι * r ^ (2 * Fintype.card ι) /
      (Fintype.card ι).factorial) := by sorry
