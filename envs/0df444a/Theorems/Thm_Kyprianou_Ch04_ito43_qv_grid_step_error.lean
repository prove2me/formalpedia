-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_qv_grid_step_error
-- name    : Kyprianou.Ch04.ito43_qv_grid_step_error
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:25:49.333037+00:00
-- url     : https://prove2.me/theorems/8989edfc-6cf9-4a74-94af-b232f907b0a3
-- title:
--   Weighted grid approximation error is bounded by grid energy
-- statement:
--   Exchange the two finite sums and apply the proved nonnegative-energy weighted approximation bound.
-- source:
--   Kyprianou (2006), Theorem 4.3 proof auxiliary

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.ito43_qv_grid_step_error
    (n m : ℕ) (u : ℕ → NNReal) (T : NNReal)
    (hu : ∀ k < n, u k ≤ T) (G : NNReal → ℝ) (e : ℕ → ℝ)
    (he : ∀ k < n, 0 ≤ e k) (δ : ℝ) (b : ℕ → NNReal) (c : ℕ → ℝ)
    (hW : ∀ s ≤ T, |G s -
      ∑ i ∈ Finset.range m, c i * (if b i ≤ s then (1:ℝ) else 0)| ≤ δ) :
    |(∑ k ∈ Finset.range n, G (u k) * e k) -
      (∑ i ∈ Finset.range m, c i *
        (∑ k ∈ Finset.range n, (if b i ≤ u k then (1:ℝ) else 0) * e k))| ≤
        δ * ∑ k ∈ Finset.range n, e k := by sorry
