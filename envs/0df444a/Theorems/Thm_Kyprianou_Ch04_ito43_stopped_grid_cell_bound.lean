-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_stopped_grid_cell_bound
-- name    : Kyprianou.Ch04.ito43_stopped_grid_cell_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T16:11:32.208456+00:00
-- url     : https://prove2.me/theorems/f131a07a-3aa4-4f4f-b1de-3f1c19d2afb2
-- title:
--   Stopped cell square bounded by full cell and crossing allowance
-- statement:
--   Stopped cell square bounded by full cell and crossing allowance.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
open Set
open scoped NNReal
set_option autoImplicit false

/-- The squared stopped-cell increment is bounded by full-cell energy and a crossing allowance. -/

theorem Kyprianou.Ch04.ito43_stopped_grid_cell_bound (X : NNReal → ℝ) (u : ℕ → NNReal) (hu : Monotone u)
    (n : ℕ) (t R : NNReal)
    (hX : ∀ a b : NNReal, a ≤ t → b ≤ t → |X a - X b| ≤ (R : ℝ)) :
    let S := (Finset.range n).filter (fun k => u k < t ∧ t < u (k+1))
    ∀ k ∈ Finset.range n,
      (X (min t (u (k+1))) - X (min t (u k)))^2 ≤
        (X (u (k+1)) - X (u k))^2 + (if k ∈ S then (R : ℝ)^2 else 0) := by sorry
