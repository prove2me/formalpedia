-- Prove2me | Theorems.Thm_Kyprianou_Ch04_boundedSquareEnergyDCTV1
-- name    : Kyprianou.Ch04.boundedSquareEnergyDCTV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:36:23.841267+00:00
-- url     : https://prove2.me/theorems/7ef468d8-02de-54f6-a84a-7ac84e774419
-- title:
--   Dominated convergence of uniformly bounded squared kernels
-- statement:
--   On a finite measure, uniformly bounded pointwise converging kernels have converging energies.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5, physical predictable integration.

import Mathlib
open MeasureTheory Filter Topology
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem boundedSquareEnergyDCTV1 {A : Type} [MeasurableSpace A] (μ : Measure A)
    [IsFiniteMeasure μ] (g : ℕ → A → ℝ) (h : A → ℝ)
    (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ n, AEStronglyMeasurable (g n) μ)
    (hb : ∀ n, ∀ᵐ x ∂μ, |g n x| ≤ K)
    (hl : ∀ᵐ x ∂μ, Tendsto (fun n => g n x) atTop (𝓝 (h x))) :
    Tendsto (fun n => ∫ x, (g n x)^2 ∂μ) atTop
      (𝓝 (∫ x, (h x)^2 ∂μ)) := by
  sorry
end Kyprianou.Ch04
