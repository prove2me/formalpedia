-- Prove2me | Theorems.Thm_GRH_dirichlet_rectangle_tail_and_derivative_bounds
-- name    : GRH.dirichlet_rectangle_tail_and_derivative_bounds
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T15:04:00.627641+00:00
-- url     : https://prove2.me/theorems/590bf782-d7ad-4bc4-ae00-1f10e786ee1f
-- title:
--   Uniform Dirichlet-polynomial tail and derivative bounds on closed critical-strip rectangles
-- statement:
--   For every nonprincipal Dirichlet character of positive level $q$, every $z$ in a rectangle with $1/2\leq a\leq\Re z\leq b\leq1$ and $|\Im z|\leq H$, and every positive integer $m$, the error of truncating at $m^2$ is at most $2q(3+2H)/m$. On the same rectangle, $|L'(z,\chi)|\leq16q(H+2)$.
-- source:
--   Derived for the centered Möbius progression bound at https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006 and its primitive nonprincipal Dirichlet input at https://prove2.me/theorems/046910d8-f152-46b2-aff5-b1c00405bcd0. Uses the published Dirichlet tail estimate at https://prove2.me/theorems/f1d91210-556c-47bf-8726-5a67ca5f667f and the Davenport bound at https://prove2.me/theorems/c5c90f21-b770-4fe2-aad6-2ead5f8ee9c0.

import Definitions.Def_GRH_DirichletGrid

open Complex Set GRH.DirichletGrid

theorem GRH.dirichlet_rectangle_tail_and_derivative_bounds (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {a b H : ℝ} (ha : (1/2:ℝ) ≤ a) (hb : b ≤ 1) (hH : 0 ≤ H)
    {m : ℕ} (hm : 0 < m) {z : ℂ} (hz : z ∈ reProdIm (Icc a b) (Icc (-H) H)) :
    ‖χ.LFunction z - sample χ m z‖ ≤ tailBudget q H / m ∧
      ‖deriv χ.LFunction z‖ ≤ slopeBudget q H := by sorry
