-- Prove2me | Theorems.Thm_GRH_dirichlet_grid_of_period_cover
-- name    : GRH.dirichlet_grid_of_period_cover
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T15:34:22.290797+00:00
-- url     : https://prove2.me/theorems/432013d2-31b5-5577-ab22-7d2b0e3cd1a0
-- title:
--   A passing arithmetic period test gives a finite Dirichlet-polynomial grid
-- statement:
--   Fix a nonprincipal character modulo $d$ and a closed rectangle $[a,b]\times[-H,H]$ with $1/2\le a\le b\le1$ and $H\ge0$. Whenever the arithmetic period test passes for $d,a,H$, a positive mesh denominator exists for which the finite Dirichlet-polynomial grid passes on the whole rectangle.
-- source:
--   Developed for the centered Möbius bound at https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006 and its primitive grid condition at https://prove2.me/theorems/a7f725ef-ecef-5ae2-855e-fc5b2d31cf0a. The centered-prefix estimate uses the published power variation bound at https://prove2.me/theorems/189b3afb-17f1-43b4-9047-0e36a164d965 and Dirichlet tail estimate at https://prove2.me/theorems/f1d91210-556c-47bf-8726-5a67ca5f667f.

import Definitions.Def_GRH_DirichletGrid
import Definitions.Def_GRH_DirichletPeriod

open GRH.DirichletGrid GRH.DirichletPeriod

theorem GRH.dirichlet_grid_of_period_cover (d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d) (hχ : χ ≠ 1)
    (a b H : ℝ) (ha : (1/2:ℝ) ≤ a) (hab : a ≤ b) (hb : b ≤ 1) (hH : 0 ≤ H)
    (hw : Covers d a H) : ∃ m : ℕ, Passes χ a b H m := by sorry
