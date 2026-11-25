-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46KilledDiscountPropertiesV1
-- name    : Kyprianou.Ch04.exercise46KilledDiscountPropertiesV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:27:22.468863+00:00
-- url     : https://prove2.me/theorems/9dcfbf72-2bcd-5454-bfca-c5662ab5d076
-- title:
--   Measurable bounded killed Laplace payoff is strictly decreasing at a positive rate
-- statement:
--   At finite times the exponential is bounded by one; the cemetery payoff is zero. Strict decrease holds for positive rates including comparison to the cemetery.
-- source:
--   Kyprianou (2006), Exercise 4.6(i).

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46KilledDiscountPropertiesV1
    (beta : Real) (hb : 0 ≤ beta) :
    let d : WithTop NNReal → Real := fun z =>
      if z = ⊤ then 0 else Real.exp (-beta * (((z.untopD 0 : NNReal) : Real)))
    Measurable d ∧ (∀ z, 0 ≤ d z ∧ d z ≤ 1) ∧
      (0 < beta → StrictAnti d) := by
  sorry
