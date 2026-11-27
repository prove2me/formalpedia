-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_real_step_left_transfer
-- name    : Kyprianou.Ch04.ito43_real_step_left_transfer
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:17:17.155505+00:00
-- url     : https://prove2.me/theorems/2439f937-4592-4ff1-91bd-a39791b6d92c
-- title:
--   Right-step approximation transfers to left limits
-- statement:
--   Every finite threshold indicator is eventually constant on a left neighbourhood; pass the uniform inequality to the left limit.
-- source:
--   Kyprianou (2006), Theorem 4.3 proof auxiliary

import Mathlib
open Set Filter
open scoped Topology ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.ito43_real_step_left_transfer
    (Y YL : ℝ → ℝ) (T : ℝ)
    (hl : ∀ s, 0 < s → s ≤ T → Tendsto Y (nhdsWithin s (Iio s)) (nhds (YL s)))
    (δ : ℝ) (m : ℕ) (b c : ℕ → ℝ)
    (h : ∀ r, 0 ≤ r → r ≤ T →
      |Y r - ∑ i ∈ Finset.range m, c i * (if b i ≤ r then (1:ℝ) else 0)| ≤ δ) :
    ∀ s, 0 < s → s ≤ T →
      |YL s - ∑ i ∈ Finset.range m, c i * (if b i < s then (1:ℝ) else 0)| ≤ δ := by sorry
