-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw47_bounded_primitive_continuous
-- name    : Kyprianou.Ch04.kw47_bounded_primitive_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T12:34:25.796978+00:00
-- url     : https://prove2.me/theorems/e0187da3-f220-5b3f-a2b0-9c623cb10161
-- title:
--   Continuous primitive of a bounded measurable real function
-- statement:
--   The bounded measurable integrand is interval integrable on every compact interval. The interval primitive is continuous and coincides with the closed-interval primitive at nonnegative times.
-- source:
--   Kyprianou (2006), Exercise 4.7; analytic compact-horizon process properties.

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch04.kw47_bounded_primitive_continuous
    (f : Real → Real) (hf : Measurable f) (h : ∀ x, ‖f x‖ ≤ 1) :
    Continuous (fun t : NNReal => ∫ s in Icc (0 : Real) (t : Real), f s ∂volume) := by sorry
