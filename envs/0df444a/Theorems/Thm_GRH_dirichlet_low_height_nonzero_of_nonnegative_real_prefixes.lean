-- Prove2me | Theorems.Thm_GRH_dirichlet_low_height_nonzero_of_nonnegative_real_prefixes
-- name    : GRH.dirichlet_low_height_nonzero_of_nonnegative_real_prefixes
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T15:03:56.403251+00:00
-- url     : https://prove2.me/theorems/cd55d898-da2f-522f-acc5-6d1de39cfb5a
-- title:
--   A zero-free neighborhood of the real interval from nonnegative real character prefixes
-- statement:
--   Suppose a nonprincipal character modulo $q$ has nonnegative real partial sums $\sum_{k=1}^n\Re\chi(k)$ at every integer cutoff. Then $L(z,\chi)\neq0$ whenever $1/2\leq\Re z\leq1$ and $|\Im z|\leq1/(256q)$. The hypothesis permits complex character values.
-- source:
--   Derived for the centered Möbius progression bound at https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006 and its primitive nonprincipal Dirichlet input at https://prove2.me/theorems/046910d8-f152-46b2-aff5-b1c00405bcd0. Uses the published Dirichlet tail estimate at https://prove2.me/theorems/f1d91210-556c-47bf-8726-5a67ca5f667f and the Davenport bound at https://prove2.me/theorems/c5c90f21-b770-4fe2-aad6-2ead5f8ee9c0.

import Definitions.Def_GRH_DirichletGrid

open Complex Set GRH.DirichletGrid

theorem GRH.dirichlet_low_height_nonzero_of_nonnegative_real_prefixes (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hp : ∀ n : ℕ, 0 ≤ ∑ k ∈ Finset.range n, (χ ((k+1:ℕ) : ZMod q)).re)
    (z : ℂ) (ha : (1/2:ℝ) ≤ z.re) (hb : z.re ≤ 1) (ht : |z.im| ≤ 1/(256*(q:ℝ))) :
    χ.LFunction z ≠ 0 := by sorry
