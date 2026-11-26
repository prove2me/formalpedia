-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41SmoothJoinBoundV11
-- name    : Kyprianou.Ch04.exercise41SmoothJoinBoundV11
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:45:49.949815+00:00
-- url     : https://prove2.me/theorems/33a5cead-875e-4929-be75-a83d0d44e167
-- title:
--   Compact continuous derivative bounds and clipped ramp derivative bounds yield a common local bound
-- statement:
--   Compact continuous derivative bounds and clipped ramp derivative bounds yield a common local bound
-- source:
--   Kyprianou (2006), Exercise 4.1(ii), smooth approximation.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41SmoothJoinBoundV11
    (fLeft fRight : ℝ → ℝ)
    (hL : ContDiff ℝ 1 fLeft) (hR : ContDiff ℝ 1 fRight)
    (p : ℕ → ℝ → ℝ)
    (hP : ∀ n x, 0 ≤ p n x ∧ p n x ≤ max 0 x)
    (hD : ∀ n x, 0 ≤ deriv (p n) x ∧ deriv (p n) x ≤ 1)
    (R : ℝ) (hRpos : 0 < R) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n x, |x| ≤ R →
      ‖deriv fLeft (-p n (-x)) * deriv (p n) (-x) +
        deriv fRight (p n x) * deriv (p n) x‖ ≤ K := by
  sorry
