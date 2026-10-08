-- Prove2me | Theorems.Thm_MillerTuckerZemlin_Formulation_feasible_x_le_one
-- name    : MillerTuckerZemlin.Formulation.feasible_x_le_one
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:15:13.531044+00:00
-- url     : https://prove2.me/theorems/ddafda85-f809-4762-97a8-bfbeaad294e2
-- title:
--   Proof of the equivalence, p. 327 — the constraints of (2) force x_ij ∈ {0, 1}
-- statement:
--   Let $n,p\ge 0$ and let $(x,u)$ be feasible for problem (2) of Miller, Tucker and Zemlin: the $x_{ij}$ ($0\le i\ne j\le n$) are non-negative integers with every column $j=1,\dots,n$ and every row $i=1,\dots,n$ summing to $1$, and $u_i-u_j+p\,x_{ij}\le p-1$ for $1\le i\ne j\le n$. Then
--
--   $$
--   x_{ij}\in\{0,1\}\qquad\text{for all } 0\le i\ne j\le n .
--   $$
--
--   This is the paper's remark "the constraints require that $x_{ij}=0$ or $1$", which makes the reading "the salesman proceeds from city $i$ to city $j$ if and only if $x_{ij}=1$" possible.
--
--   **Formalization Note** The statement is $x_{ij}\le 1$ for all $i,j$ in $\{0,\dots,n\}$; together with $x_{ij}\in\mathbb N$ this is $x_{ij}\in\{0,1\}$. On the diagonal, $x_{ii}=0$ is part of the encoding of (2) (there is no variable $x_{ii}$).
-- source:
--   Miller, Tucker, Zemlin, Integer Programming Formulation of Traveling Salesman Problems, J. ACM 7(4) (1960), p. 327, proof of the equivalence, "Note that the constraints require that x_ij = 0 or 1"

import Mathlib
import Definitions.Def_MillerTuckerZemlin_Formulation_Model

namespace MillerTuckerZemlin.Formulation

theorem feasible_x_le_one (n p : ℕ) (x : Fin (n + 1) → Fin (n + 1) → ℕ) (u : Fin (n + 1) → ℝ)
    (hx : Feasible n p x u) : ∀ i j : Fin (n + 1), x i j ≤ 1 := by sorry

end MillerTuckerZemlin.Formulation
