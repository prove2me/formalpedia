-- Prove2me | Theorems.Thm_GlobalTheory_volume_closedBall_euclideanSpace_complex
-- name    : GlobalTheory.volume_closedBall_euclideanSpace_complex
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:24:42.603654+00:00
-- url     : https://prove2.me/theorems/7764e676-3edb-40f5-abbb-f183cd77c829
-- title:
--   Global Theory: volume closed Ball euclidean Space complex
-- statement:
--   The Global Theory construction uses the volume closed Ball euclidean Space complex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EnormPowLeInvMeasureMulLintegralBall.lean#L282-L287
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EnormPowLeInvMeasureMulLintegralBall.lean#L282-L287

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

theorem GlobalTheory.volume_closedBall_euclideanSpace_complex (a : EuclideanSpace ℂ ι) {r : ℝ} (hr : 0 < r) :
    volume (closedBall a r) = ENNReal.ofReal (π ^ Fintype.card ι * r ^ (2 * Fintype.card ι) /
      (Fintype.card ι).factorial) := by sorry
