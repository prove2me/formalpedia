-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41PassLimitV7
-- name    : Kyprianou.Ch04.exercise41PassLimitV7
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:14:37.833215+00:00
-- url     : https://prove2.me/theorems/1ac38560-51d6-4c8e-888f-20febd34df45
-- title:
--   Dominated convergence for the drift integral and Tannery for the jump series
-- statement:
--   Dominated convergence for the drift integral and Tannery for the jump series
-- source:
--   Kyprianou (2006), Exercise 4.1(ii).

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators Classical
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41PassLimitV7
    {ι : Type} (μ : Measure ℝ)
    (g : ℕ → ℝ → ℝ) (G : ℝ → ℝ)
    (x0 xt d : ℝ) (D : ℕ → ℝ → ℝ) (D0 : ℝ → ℝ)
    (J : ℕ → ι → ℝ) (J0 : ι → ℝ) (K : ℝ → ℝ) (B : ι → ℝ)
    (h0 : Tendsto (fun n => g n x0) atTop (𝓝 (G x0)))
    (ht : Tendsto (fun n => g n xt) atTop (𝓝 (G xt)))
    (hm : ∀ n, AEStronglyMeasurable (D n) μ)
    (hK : Integrable K μ)
    (hDb : ∀ n, ∀ᵐ s ∂μ, ‖D n s‖ ≤ K s)
    (hDl : ∀ᵐ s ∂μ, Tendsto (fun n => D n s) atTop (𝓝 (D0 s)))
    (hB : Summable B)
    (hJl : ∀ k, Tendsto (fun n => J n k) atTop (𝓝 (J0 k)))
    (hJb : ∀ᶠ n in atTop, ∀ k, ‖J n k‖ ≤ B k)
    (hEq : ∀ n, g n xt = g n x0 +
      d * (∫ s, D n s ∂μ) + ∑' k, J n k) :
    G xt = G x0 + d * (∫ s, D0 s ∂μ) + ∑' k, J0 k := by
  sorry
