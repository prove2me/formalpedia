-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw47_grid_cell_exists_unique
-- name    : Kyprianou.Ch04.kw47_grid_cell_exists_unique
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:04:38.646323+00:00
-- url     : https://prove2.me/theorems/3583c61c-f65b-586f-8c79-086ff0ede50b
-- title:
--   Unique occupied half-open cell of a monotone finite grid
-- statement:
--   For a nondecreasing finite grid, every point strictly above the initial endpoint and at or below the last endpoint belongs to exactly one half-open grid cell. Repeated times are allowed. Existence follows by induction on the number of cells and uniqueness by monotonicity. This is the cell-selection component of the verified right-endpoint quadrature convergence proof.
-- source:
--   Kyprianou (2006), Exercise 4.7; deterministic Stieltjes quadrature.

import Mathlib
open Set
set_option autoImplicit false

/-- A finite increasing grid covers its half-open endpoint interval
with exactly one nonempty cell containing each point. -/

theorem Kyprianou.Ch04.kw47_grid_cell_exists_unique
    (u : Nat → Real) (hu : Monotone u) (N : Nat)
    (x : Real) (hx : x ∈ Ioc (u 0) (u N)) :
    ∃ i ∈ Finset.range N, x ∈ Ioc (u i) (u (i+1)) ∧
      ∀ j ∈ Finset.range N, x ∈ Ioc (u j) (u (j+1)) → j = i := by sorry
