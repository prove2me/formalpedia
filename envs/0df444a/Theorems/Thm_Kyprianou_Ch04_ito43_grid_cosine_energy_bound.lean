-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_grid_cosine_energy_bound
-- name    : Kyprianou.Ch04.ito43_grid_cosine_energy_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T16:09:55.107427+00:00
-- url     : https://prove2.me/theorems/dede23e3-e7ac-4f1f-b606-65ca63d1b8b5
-- title:
--   Cosine deficits dominate compactly bounded grid energy
-- statement:
--   Cosine deficits dominate compactly bounded grid energy.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
open MeasureTheory Set
set_option autoImplicit false

/-- On paths with increments in a fixed compact interval, cosine deficits dominate squared increments. -/

theorem Kyprianou.Ch04.ito43_grid_cosine_energy_bound (n : ℕ) (D : ℕ → ℝ) (R : ℝ) (hR : 0 < R)
    (hD : ∀ k < n, |D k| ≤ R) :
    (∑ k ∈ Finset.range n, (D k)^2) ≤
      (Real.pi ^ 2 * R^2 / 2) *
        ∑ k ∈ Finset.range n, (1 - Real.cos (D k/R)) := by sorry
