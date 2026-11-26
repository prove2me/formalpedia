-- Prove2me | Theorems.Thm_GRH_conductors_three_four_low_height_nonzero
-- name    : GRH.conductors_three_four_low_height_nonzero
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T15:04:00.844218+00:00
-- url     : https://prove2.me/theorems/64904a2f-3373-4fe0-b77b-696d639c6dbb
-- title:
--   Nonprincipal Dirichlet L-functions of levels three and four are nonzero at small heights
-- statement:
--   For every nonprincipal complex Dirichlet character at level $q=3$ or $q=4$, $L(z,\chi)$ is nonzero on the entire closed rectangle $1/2\leq\Re z\leq1$, $|\Im z|\leq1/(256q)$. The two heights are $1/768$ and $1/1024$, respectively.
-- source:
--   Derived for the centered Möbius progression bound at https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006 and its primitive nonprincipal Dirichlet input at https://prove2.me/theorems/046910d8-f152-46b2-aff5-b1c00405bcd0. Uses the published Dirichlet tail estimate at https://prove2.me/theorems/f1d91210-556c-47bf-8726-5a67ca5f667f and the Davenport bound at https://prove2.me/theorems/c5c90f21-b770-4fe2-aad6-2ead5f8ee9c0.

import Definitions.Def_GRH_DirichletGrid

open Complex Set GRH.DirichletGrid

theorem GRH.conductors_three_four_low_height_nonzero (q : ℕ) [NeZero q] (hq : q = 3 ∨ q = 4)
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (z : ℂ)
    (ha : (1/2:ℝ) ≤ z.re) (hb : z.re ≤ 1) (ht : |z.im| ≤ 1/(256*(q:ℝ))) :
    χ.LFunction z ≠ 0 := by sorry
