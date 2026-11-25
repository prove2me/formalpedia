-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw47_capped_uniform_grid
-- name    : Kyprianou.Ch04.kw47_capped_uniform_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:09:34.391665+00:00
-- url     : https://prove2.me/theorems/ec433da3-00b6-441e-9b12-ad36e96baa6a
-- title:
--   Monotone capped equal time grids with vanishing mesh
-- statement:
--   The capped equal subdivision of an interval in nonnegative real time is monotone, starts and ends at its prescribed endpoints, is bounded throughout by the terminal time, and has exact equal mesh in real coordinates tending to zero. This also covers intervals of zero length and supports the product-grid conditional centring and convergence arguments.
-- source:
--   Kyprianou (2006), Exercise 4.7, deterministic time grid.

import Mathlib
open Filter Topology
open scoped NNReal
set_option autoImplicit false

/-- The capped equal subdivision supplies monotone bounded grids and
a real mesh tending to zero, including zero-length intervals. -/

theorem Kyprianou.Ch04.kw47_capped_uniform_grid
    (a b : NNReal) (hab : a ≤ b) :
    let u : Nat → Nat → NNReal := fun n i =>
      a + (b - a) * ((min i (n+1) : Nat) : NNReal) / ((n+1 : Nat) : NNReal)
    (∀ n, Monotone (u n)) ∧
    (∀ n, u n 0 = a) ∧
    (∀ n, u n (n+1) = b) ∧
    (∀ n i, u n i ≤ b) ∧
    (∀ n i, i < n+1 →
      (u n (i+1) : Real) - (u n i : Real) =
        ((b : Real) - (a : Real)) / ((n+1 : Nat) : Real)) ∧
    Tendsto (fun n : Nat => ((b : Real)-(a : Real)) /
      ((n+1 : Nat) : Real)) atTop (nhds 0) := by sorry
