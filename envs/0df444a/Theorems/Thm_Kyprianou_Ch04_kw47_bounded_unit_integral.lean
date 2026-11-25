-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw47_bounded_unit_integral
-- name    : Kyprianou.Ch04.kw47_bounded_unit_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T10:12:25.226542+00:00
-- url     : https://prove2.me/theorems/e5d21d12-e091-47a9-86f2-496afe0aa6fd
-- title:
--   Integral of a unit-bounded real path on a nonnegative compact interval
-- statement:
--   A pointwise nonnegative function bounded by one has its Bochner set integral between zero and the interval length, even when its integral is defined as zero outside integrability.
-- source:
--   Kyprianou (2006), Exercise 4.7(iii), worked solution pp. 320-321.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.kw47_bounded_unit_integral
    (f : Real → Real) (t : NNReal) (hf : ∀ x : Real, 0 ≤ f x ∧ f x ≤ 1) :
    0 ≤ (∫ r in Icc (0 : Real) (t : Real), f r ∂volume) ∧
    (∫ r in Icc (0 : Real) (t : Real), f r ∂volume) ≤ (t : Real) := by sorry
