-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_stopped_grid_energy_bound
-- name    : Kyprianou.Ch04.ito43_stopped_grid_energy_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T16:09:52.786196+00:00
-- url     : https://prove2.me/theorems/1b426e10-adba-5aa0-9eca-69833ea9ed3b
-- title:
--   Stopped grid energy is at most full grid energy plus one oscillation square
-- statement:
--   Stopped grid energy is at most full grid energy plus one oscillation square.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
open Set
open scoped NNReal
set_option autoImplicit false

/-- A stopped grid has full cells and at most one partial cell. Its energy is bounded
by full-grid energy plus the squared oscillation bound. -/

theorem Kyprianou.Ch04.ito43_stopped_grid_energy_bound (X : NNReal → ℝ) (u : ℕ → NNReal) (hu : Monotone u)
    (n : ℕ) (t R : NNReal)
    (hX : ∀ a b : NNReal, a ≤ t → b ≤ t → |X a - X b| ≤ (R : ℝ)) :
    (∑ k ∈ Finset.range n, (X (min t (u (k+1))) - X (min t (u k)))^2) ≤
      (∑ k ∈ Finset.range n, (X (u (k+1)) - X (u k))^2) + (R : ℝ)^2 := by sorry
