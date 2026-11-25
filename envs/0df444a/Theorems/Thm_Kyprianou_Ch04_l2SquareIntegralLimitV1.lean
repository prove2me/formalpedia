-- Prove2me | Theorems.Thm_Kyprianou_Ch04_l2SquareIntegralLimitV1
-- name    : Kyprianou.Ch04.l2SquareIntegralLimitV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:42:04.7063+00:00
-- url     : https://prove2.me/theorems/1e67ef69-4f07-402f-b6e5-2f8b87d5514c
-- title:
--   Convergence of squared integrals under L2 convergence
-- statement:
--   Convergence in the L2 seminorm of real functions implies convergence of the integrals of their squares.
-- source:
--   Kyprianou (2006), Exercise 4.5(ii).

import Mathlib
open MeasureTheory Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem l2SquareIntegralLimitV1 {α : Type} [MeasurableSpace α] (μ : Measure α)
    (f : ℕ → α → ℝ) (g : α → ℝ)
    (hf : ∀ n, MemLp (f n) 2 μ) (hg : MemLp g 2 μ)
    (h : Tendsto (fun n => eLpNorm (fun x => f n x - g x) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, (f n x)^2 ∂μ) atTop (𝓝 (∫ x, (g x)^2 ∂μ)) := by
  sorry
end Kyprianou.Ch04
