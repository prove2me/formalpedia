-- Prove2me | Theorems.Thm_GlobalTheory_preimage_toLp_ball_complex
-- name    : GlobalTheory.preimage_toLp_ball_complex
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:14:39.313405+00:00
-- url     : https://prove2.me/theorems/ed9d2241-8fcf-4d85-a1fb-70c5c3604f9e
-- title:
--   Global Theory: preimage to Lp ball complex
-- statement:
--   The Global Theory construction uses the preimage to Lp ball complex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EnormPowLeInvMeasureMulLintegralBall.lean#L318-L322
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EnormPowLeInvMeasureMulLintegralBall.lean#L318-L322

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

theorem GlobalTheory.preimage_toLp_ball_complex {r : ℝ} (hr : 0 < r) :
    (WithLp.toLp 2 : (ι → ℂ) → EuclideanSpace ℂ ι) ⁻¹' ball 0 r =
      {x : ι → ℂ | ∑ i, ‖x i‖ ^ 2 < r ^ 2} := by sorry
