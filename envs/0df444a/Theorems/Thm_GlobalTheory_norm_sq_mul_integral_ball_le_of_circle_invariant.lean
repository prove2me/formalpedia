-- Prove2me | Theorems.Thm_GlobalTheory_norm_sq_mul_integral_ball_le_of_circle_invariant
-- name    : GlobalTheory.norm_sq_mul_integral_ball_le_of_circle_invariant
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:13:08.195578+00:00
-- url     : https://prove2.me/theorems/6d17e249-dd84-4d5f-bb7f-1ce35698ab81
-- title:
--   Global Theory: norm sq mul integral ball le of circle invariant
-- statement:
--   The Global Theory construction uses the norm sq mul integral ball le of circle invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormSqMulIntegralBallLeOfCircleInvariant.lean#L10-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormSqMulIntegralBallLeOfCircleInvariant.lean#L10-L46

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EnormPowLeInvMeasureMulLintegralBall
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormSqMulIntegralBallLeOfCircleInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder
open GlobalTheory

theorem GlobalTheory.norm_sq_mul_integral_ball_le_of_circle_invariant :
    ∀ (n : ℕ) (δ : ℝ) (U : Set (V n)) (f : V n → ℂ) (W : V n → ℝ), 0 < δ → IsOpen U →
      closedBall 0 δ ⊆ U → DifferentiableOn ℂ f U → ContinuousOn W (closedBall 0 δ) →
      (∀ w, 0 ≤ W w) → (∀ (θ : ℂ) (w : V n), ‖θ‖ = 1 → W (θ • w) = W w) →
      ‖f 0‖ ^ 2 * ∫ w in ball (0 : V n) δ, W w ≤ ∫ w in ball (0 : V n) δ, ‖f w‖ ^ 2 * W w := by sorry
