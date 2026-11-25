-- Prove2me | Theorems.Thm_Kyprianou_Ch04_l2NormSquareIntegralV1
-- name    : Kyprianou.Ch04.l2NormSquareIntegralV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:37:29.470703+00:00
-- url     : https://prove2.me/theorems/685b3533-a334-4a12-b17a-6ee869e9a7ff
-- title:
--   Square of real L2 norm equals integrated square
-- statement:
--   For a real square-integrable function, its squared L2 norm equals its integrated square.
-- source:
--   Kyprianou (2006), Exercise 4.5(ii); finite marked Poisson moment calculation.

import Mathlib
open MeasureTheory Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem l2NormSquareIntegralV1 {α : Type} [MeasurableSpace α] (μ : Measure α)
    (g : α → ℝ) (hg : MemLp g 2 μ) :
    (eLpNorm g 2 μ).toReal ^ 2 = ∫ x, (g x)^2 ∂μ := by
  sorry
end Kyprianou.Ch04
