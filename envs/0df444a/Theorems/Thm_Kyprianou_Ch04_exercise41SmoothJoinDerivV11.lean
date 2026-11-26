-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41SmoothJoinDerivV11
-- name    : Kyprianou.Ch04.exercise41SmoothJoinDerivV11
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:45:51.546855+00:00
-- url     : https://prove2.me/theorems/8218e001-66db-49d9-95fc-b2cdbff182c0
-- title:
--   C1 regularity and exact derivative of two smooth positive-part compositions
-- statement:
--   C1 regularity and exact derivative of two smooth positive-part compositions
-- source:
--   Kyprianou (2006), Exercise 4.1(ii), smooth approximation.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41SmoothJoinDerivV11
    (fLeft fRight : ℝ → ℝ)
    (hL : ContDiff ℝ 1 fLeft) (hR : ContDiff ℝ 1 fRight)
    (p : ℝ → ℝ) (hp : ContDiff ℝ 1 p) :
    let g := fun x : ℝ => fLeft (-p (-x)) - fLeft 0 +
      fRight (p x) - fRight 0
    ContDiff ℝ 1 g ∧ ∀ x, deriv g x =
      deriv fLeft (-p (-x)) * deriv p (-x) +
      deriv fRight (p x) * deriv p x := by
  sorry
