-- Prove2me | Theorems.Thm_GRH_dirichlet_prefix_unit_count_bound
-- name    : GRH.dirichlet_prefix_unit_count_bound
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T16:15:52.804409+00:00
-- url     : https://prove2.me/theorems/0641872a-28c3-4778-87a3-00bc70febc36
-- title:
--   Forward and backward unit counts bound centered character prefixes in every period
-- statement:
--   For any nonprincipal Dirichlet character modulo $q$, let $A_n=\sum_{k=1}^n\chi(k)$. At $r=n\bmod q=0$, $|A_n-1|=1$. For $r>0$, let $j$ count the unit residues in $1,\ldots,r$. Then $|A_n-1|\le\min(j-1,\varphi(q)+1-j)$.
-- source:
--   Developed for the centered Möbius theorem at https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006 and its open primitive grid condition at https://prove2.me/theorems/59bf325f-868f-5552-94bb-1b5f67435396. Uses the centered Abel estimate at https://prove2.me/theorems/3b5a3db7-3b41-46b5-a41d-4a78754ad8d2 and the power variation estimate at https://prove2.me/theorems/189b3afb-17f1-43b4-9047-0e36a164d965.

import Definitions.Def_GRH_DirichletPrefix

open GRH.DirichletPrefix

theorem GRH.dirichlet_prefix_unit_count_bound (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (n : ℕ) :
    ‖(∑ k ∈ Finset.range n, χ ((k+1:ℕ):ZMod q))-1‖ ≤ (weight q n:ℝ) := by sorry
