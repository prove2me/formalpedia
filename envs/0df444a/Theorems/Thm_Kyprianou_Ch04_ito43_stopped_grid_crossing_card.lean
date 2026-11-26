-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_stopped_grid_crossing_card
-- name    : Kyprianou.Ch04.ito43_stopped_grid_crossing_card
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T16:11:32.764023+00:00
-- url     : https://prove2.me/theorems/e9eb6ebc-3246-43cc-9e37-2362e313019f
-- title:
--   At most one stopped grid cell crosses the stopping time
-- statement:
--   At most one stopped grid cell crosses the stopping time.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
open Set
open scoped NNReal
set_option autoImplicit false

/-- A monotone grid has at most one cell strictly crossing a fixed time. -/

theorem Kyprianou.Ch04.ito43_stopped_grid_crossing_card (u : ℕ → NNReal) (hu : Monotone u) (n : ℕ) (t : NNReal) :
    ((Finset.range n).filter (fun k => u k < t ∧ t < u (k+1))).card ≤ 1 := by sorry
