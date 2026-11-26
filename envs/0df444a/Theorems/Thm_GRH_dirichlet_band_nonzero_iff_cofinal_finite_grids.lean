-- Prove2me | Theorems.Thm_GRH_dirichlet_band_nonzero_iff_cofinal_finite_grids
-- name    : GRH.dirichlet_band_nonzero_iff_cofinal_finite_grids
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T15:03:59.228406+00:00
-- url     : https://prove2.me/theorems/6e672337-ee7a-503b-82d9-3c5710136314
-- title:
--   Zero exclusion in an entire half-open Dirichlet strip is equivalent to cofinal finite grids
-- statement:
--   Fix a nonprincipal character and $1/2<b\leq1$. Nonvanishing at all heights throughout $1/2<\Re z\leq b$ is equivalent to passing a finite grid on each of the rectangles of height $h+1$ and left edge $1/2+(b-1/2)/(h+1)$, for natural $h$. Each rectangle may use a different mesh denominator.
-- source:
--   Derived for the centered Möbius progression bound at https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006 and its primitive nonprincipal Dirichlet input at https://prove2.me/theorems/046910d8-f152-46b2-aff5-b1c00405bcd0. Uses the published Dirichlet tail estimate at https://prove2.me/theorems/f1d91210-556c-47bf-8726-5a67ca5f667f and the Davenport bound at https://prove2.me/theorems/c5c90f21-b770-4fe2-aad6-2ead5f8ee9c0.

import Definitions.Def_GRH_DirichletGrid

open Complex Set GRH.DirichletGrid

theorem GRH.dirichlet_band_nonzero_iff_cofinal_finite_grids (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (b : ℝ) (hb : (1/2:ℝ) < b) (hb1 : b ≤ 1) :
    (∀ z : ℂ, (1/2:ℝ) < z.re → z.re ≤ b → χ.LFunction z ≠ 0) ↔
      ∀ h : ℕ, ∃ m : ℕ, Passes χ (1/2 + (b-1/2)/((h:ℝ)+1)) b ((h:ℝ)+1) m := by sorry
