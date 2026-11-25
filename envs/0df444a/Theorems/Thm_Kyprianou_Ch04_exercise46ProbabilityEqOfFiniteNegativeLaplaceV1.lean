-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46ProbabilityEqOfFiniteNegativeLaplaceV1
-- name    : Kyprianou.Ch04.exercise46ProbabilityEqOfFiniteNegativeLaplaceV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:57:43.439653+00:00
-- url     : https://prove2.me/theorems/c8e42e90-8656-45d2-afef-dc0aefd956d1
-- title:
--   Finite negative Laplace transforms identify probability measures
-- statement:
--   Reflect both laws, use finite positive moment generating functions and uniqueness, and reflect back.
-- source:
--   Kyprianou (2006), Exercise 4.6(iii).

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46ProbabilityEqOfFiniteNegativeLaplaceV1
    (nu eta : Measure Real) [IsProbabilityMeasure nu] [IsProbabilityMeasure eta]
    (hfin : ∀ s : Real, 0 < s →
      (∫⁻ x : Real, ENNReal.ofReal (Real.exp (-s*x)) ∂nu) < ⊤)
    (heq : ∀ s : Real, 0 < s →
      (∫⁻ x : Real, ENNReal.ofReal (Real.exp (-s*x)) ∂nu) =
      (∫⁻ x : Real, ENNReal.ofReal (Real.exp (-s*x)) ∂eta)) :
    nu = eta := by
  sorry
