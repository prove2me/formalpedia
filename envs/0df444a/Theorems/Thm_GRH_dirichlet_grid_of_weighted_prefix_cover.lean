-- Prove2me | Theorems.Thm_GRH_dirichlet_grid_of_weighted_prefix_cover
-- name    : GRH.dirichlet_grid_of_weighted_prefix_cover
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T16:15:52.252565+00:00
-- url     : https://prove2.me/theorems/45583b27-f879-56b6-9877-5ba79615e91e
-- title:
--   Weighted character-prefix covers give finite Dirichlet-polynomial grids
-- statement:
--   A weighted-prefix cover at $d,a,b,H$ gives a passing finite Dirichlet-polynomial grid for every nonprincipal character modulo $d$, provided $1/2\le a\le b\le1$ and $H\ge0$. One mesh denominator certifies the closed rectangle.
-- source:
--   Developed for the centered Möbius theorem at https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006 and its open primitive grid condition at https://prove2.me/theorems/59bf325f-868f-5552-94bb-1b5f67435396. Uses the centered Abel estimate at https://prove2.me/theorems/3b5a3db7-3b41-46b5-a41d-4a78754ad8d2 and the power variation estimate at https://prove2.me/theorems/189b3afb-17f1-43b4-9047-0e36a164d965.

import Definitions.Def_GRH_DirichletGrid
import Definitions.Def_GRH_DirichletPrefix

open GRH.DirichletGrid GRH.DirichletPrefix

theorem GRH.dirichlet_grid_of_weighted_prefix_cover (d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d) (hχ : χ ≠ 1)
    (a b H : ℝ) (ha : (1/2:ℝ) ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    (hH : 0 ≤ H) (hw : Covers d a b H) : ∃ m : ℕ, Passes χ a b H m := by sorry
