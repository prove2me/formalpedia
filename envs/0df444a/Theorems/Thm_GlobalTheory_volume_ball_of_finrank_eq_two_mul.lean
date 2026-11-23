-- Prove2me | Theorems.Thm_GlobalTheory_volume_ball_of_finrank_eq_two_mul
-- name    : GlobalTheory.volume_ball_of_finrank_eq_two_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:11:26.596411+00:00
-- url     : https://prove2.me/theorems/0f27837e-53f9-4010-9a50-d6e837caf42a
-- title:
--   Global Theory: volume ball of finrank eq two mul
-- statement:
--   The Global Theory construction uses the volume ball of finrank eq two mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EnormPowLeInvMeasureMulLintegralBall.lean#L221-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EnormPowLeInvMeasureMulLintegralBall.lean#L221-L238

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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem GlobalTheory.volume_ball_of_finrank_eq_two_mul {D : ℕ} (hD : Module.finrank ℝ E = 2 * D) (a : E)
    {r : ℝ} (hr : 0 < r) :
    volume (ball a r) = ENNReal.ofReal (π ^ D * r ^ (2 * D) / D.factorial) := by sorry
