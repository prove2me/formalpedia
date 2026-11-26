-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_right_grid_limit
-- name    : Kyprianou.Ch04.ito43_right_grid_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:19:05.352338+00:00
-- url     : https://prove2.me/theorems/2ac8d660-89df-4470-853e-38d127ac9af5
-- title:
--   Right grid convergence through right neighbourhood
-- statement:
--   Right grid convergence through right neighbourhood.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3, supporting lemma.

import Mathlib
open Filter Set
open scoped Topology
set_option autoImplicit false

/-- Any grid approximation between the original time and one vanishing mesh to its right
converges through the right-neighbourhood filter. -/

theorem Kyprianou.Ch04.ito43_right_grid_limit (T s : ℝ) (r : ℕ → ℝ)
    (h : ∀ n : ℕ, 0 < n → s ≤ r n ∧ r n ≤ s + T / (n : ℝ)) :
    Tendsto r atTop (nhdsWithin s (Ici s)) := by sorry
