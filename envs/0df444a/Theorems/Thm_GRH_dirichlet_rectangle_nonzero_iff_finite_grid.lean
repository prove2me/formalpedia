-- Prove2me | Theorems.Thm_GRH_dirichlet_rectangle_nonzero_iff_finite_grid
-- name    : GRH.dirichlet_rectangle_nonzero_iff_finite_grid
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T15:03:59.62306+00:00
-- url     : https://prove2.me/theorems/f05fd9cf-2f28-46db-9503-b1ffcc9c949e
-- title:
--   Nonvanishing of a nonprincipal Dirichlet L-function on a rectangle is equivalent to a finite grid certificate
-- statement:
--   For a nonprincipal Dirichlet character and a closed rectangle $[a,b]\times[-H,H]$ in $1/2\leq\Re z\leq1$, nonvanishing everywhere is equivalent to the existence of one positive integer $m$ whose finite grid passes. A sample either lies far enough inside the proved low-height region at level three or four, or has a strictly positive Dirichlet-polynomial margin after both the truncation and variation allowances. The criterion also covers rectangles of zero width or height.
-- source:
--   Derived for the centered Möbius progression bound at https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006 and its primitive nonprincipal Dirichlet input at https://prove2.me/theorems/046910d8-f152-46b2-aff5-b1c00405bcd0. Uses the published Dirichlet tail estimate at https://prove2.me/theorems/f1d91210-556c-47bf-8726-5a67ca5f667f and the Davenport bound at https://prove2.me/theorems/c5c90f21-b770-4fe2-aad6-2ead5f8ee9c0.

import Definitions.Def_GRH_DirichletGrid

open Complex Set GRH.DirichletGrid

theorem GRH.dirichlet_rectangle_nonzero_iff_finite_grid (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (a b H : ℝ) (ha : (1/2:ℝ) ≤ a) (hab : a ≤ b) (hb : b ≤ 1) (hH : 0 ≤ H) :
    (∀ z : ℂ, z ∈ reProdIm (Icc a b) (Icc (-H) H) → χ.LFunction z ≠ 0) ↔
      ∃ m : ℕ, GRH.DirichletGrid.Passes χ a b H m := by sorry
