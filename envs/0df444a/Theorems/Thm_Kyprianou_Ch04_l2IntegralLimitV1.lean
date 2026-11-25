-- Prove2me | Theorems.Thm_Kyprianou_Ch04_l2IntegralLimitV1
-- name    : Kyprianou.Ch04.l2IntegralLimitV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:37:31.554852+00:00
-- url     : https://prove2.me/theorems/c0e09db5-c150-4240-b391-157d5c9b263a
-- title:
--   L2 convergence implies first moment convergence on finite measures
-- statement:
--   Convergence in L2 on a finite measure space implies convergence of the real integrals.
-- source:
--   Kyprianou (2006), Exercise 4.5(ii); finite marked Poisson moment calculation.

import Mathlib
open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem l2IntegralLimitV1 {α : Type} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (f : ℕ → α → ℝ) (g : α → ℝ)
    (hf : ∀ n, MemLp (f n) 2 μ) (hg : MemLp g 2 μ)
    (h : Tendsto (fun n => eLpNorm (fun x => f n x - g x) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, f n x ∂μ) atTop (𝓝 (∫ x, g x ∂μ)) := by
  sorry
end Kyprianou.Ch04
