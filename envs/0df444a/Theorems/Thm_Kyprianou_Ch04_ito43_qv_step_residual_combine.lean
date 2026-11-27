-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_qv_step_residual_combine
-- name    : Kyprianou.Ch04.ito43_qv_step_residual_combine
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:29:05.835259+00:00
-- url     : https://prove2.me/theorems/82b450d8-f7c4-4d2a-bcec-0f153c5cdbb2
-- title:
--   Three step approximation errors combine linearly
-- statement:
--   Separate the three weighted approximation errors and apply the triangle inequality.
-- source:
--   Kyprianou (2006), Theorem 4.3 proof auxiliary

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.ito43_qv_step_residual_combine
    (σ δ T J Q A B G : ℝ) (hσ : 0 ≤ σ)
    (m : ℕ) (c a j q : ℕ → ℝ)
    (ha : |A-∑ i ∈ Finset.range m, c i*a i| ≤ δ*T)
    (hb : |B-∑ i ∈ Finset.range m, c i*j i| ≤ δ*J)
    (hg : |G-∑ i ∈ Finset.range m, c i*q i| ≤ δ*Q) :
    |σ*A+B-G - ∑ i ∈ Finset.range m, c i*(σ*a i+j i-q i)| ≤
      δ*(σ*T+J+Q) := by sorry
