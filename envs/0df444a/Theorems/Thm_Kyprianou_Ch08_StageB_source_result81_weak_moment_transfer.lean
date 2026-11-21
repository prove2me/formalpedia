-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_weak_moment_transfer
-- name    : Kyprianou.Ch08.StageB.source_result81_weak_moment_transfer
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T19:42:18.840114+00:00
-- url     : https://prove2.me/theorems/8faba3d8-a099-4bce-b215-93e811383852
-- title:
--   Weak convergence transfers a continuous moment with a square bound
-- statement:
--   If the integrals of a nonnegative continuous function under weakly convergent probability laws converge and its second moments are eventually bounded, the limiting integral equals the integral under the weak limit.
-- source:
--   Moment convergence lemma for the finite-jump approximation in Kyprianou, Chapter 8, Theorem 8.1. Parent Prove2Me theorem 99139220-c85a-4a27-bbce-f437a4e7240e.

import Mathlib.MeasureTheory.Measure.Portmanteau
open MeasureTheory Filter
open scoped ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.source_result81_weak_moment_transfer
    (μs : ℕ → ProbabilityMeasure ℝ) (μ : ProbabilityMeasure ℝ)
    (hweak : Tendsto μs atTop (nhds μ))
    (f : ℝ → ℝ) (hf : Continuous f) (hfn : ∀ x, 0 ≤ f x)
    (hint : ∀ n, Integrable f (μs n : Measure ℝ)) (C L : ℝ)
    (hsq : ∀ᶠ n in atTop, Integrable (fun x => f x ^ 2) (μs n : Measure ℝ) ∧
      (∫ x, f x ^ 2 ∂(μs n : Measure ℝ)) ≤ C)
    (hL : Tendsto (fun n => ∫ x, f x ∂(μs n : Measure ℝ)) atTop (nhds L)) :
    Integrable f (μ : Measure ℝ) ∧ (∫ x, f x ∂(μ : Measure ℝ)) = L := by
  sorry
