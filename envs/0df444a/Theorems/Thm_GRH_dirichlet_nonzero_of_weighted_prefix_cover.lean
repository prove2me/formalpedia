-- Prove2me | Theorems.Thm_GRH_dirichlet_nonzero_of_weighted_prefix_cover
-- name    : GRH.dirichlet_nonzero_of_weighted_prefix_cover
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T16:15:53.66538+00:00
-- url     : https://prove2.me/theorems/7cc14f1b-cab3-401b-a3d3-4d1dd0645497
-- title:
--   A weighted prefix cover excludes all nonprincipal Dirichlet zeros on its rectangle
-- statement:
--   For a nonprincipal character modulo $d$, a weighted-prefix cover at $d,a,b,H$ implies $L(s,\chi)\ne0$ for every $s$ with $a\le\Re s\le b$ and $|\Im s|\le H$. The witness may use an arbitrary multiple of $d$.
-- source:
--   Developed for the centered Möbius theorem at https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006 and its open primitive grid condition at https://prove2.me/theorems/59bf325f-868f-5552-94bb-1b5f67435396. Uses the centered Abel estimate at https://prove2.me/theorems/3b5a3db7-3b41-46b5-a41d-4a78754ad8d2 and the power variation estimate at https://prove2.me/theorems/189b3afb-17f1-43b4-9047-0e36a164d965.

import Definitions.Def_GRH_DirichletPrefix

open GRH.DirichletPrefix

theorem GRH.dirichlet_nonzero_of_weighted_prefix_cover (d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d) (hχ : χ ≠ 1)
    (a b H : ℝ) (hw : Covers d a b H)
    (s : ℂ) (ha : a ≤ s.re) (hb : s.re ≤ b) (ht : |s.im| ≤ H) : χ.LFunction s ≠ 0 := by sorry
