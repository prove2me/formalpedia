-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_partition_threshold_sum
-- name    : Kyprianou.Ch04.ito43_partition_threshold_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:17:16.656919+00:00
-- url     : https://prove2.me/theorems/af9c265d-ea95-4eae-ae33-181280f2db7c
-- title:
--   Finite threshold sum telescopes on its grid interval
-- statement:
--   Induct on the grid length, using monotonicity and telescoping consecutive values.
-- source:
--   Kyprianou (2006), Theorem 4.3 proof auxiliary

import Mathlib
open Set Filter
open scoped Topology ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.ito43_partition_threshold_sum
    (p : ℕ → ℝ) (hp : Monotone p) (Y : ℝ → ℝ)
    (n : ℕ) (s : ℝ) (h0 : p 0 ≤ s) (hn : s < p n) :
    ∃ j < n, p j ≤ s ∧ s < p (j+1) ∧
      (∑ i ∈ Finset.range (n+1),
        (if i=0 then Y (p 0) else Y (p i)-Y (p (i-1))) *
        (if p i ≤ s then (1:ℝ) else 0)) = Y (p j) := by sorry
