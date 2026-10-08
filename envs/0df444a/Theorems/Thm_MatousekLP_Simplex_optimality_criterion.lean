-- Prove2me | Theorems.Thm_MatousekLP_Simplex_optimality_criterion
-- name    : MatousekLP.Simplex.optimality_criterion
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T21:03:14.652165+00:00
-- url     : https://prove2.me/theorems/a0d30973-52a5-48e3-bf52-60b45546ed31
-- title:
--   Optimality criterion — a tableau with $r \le 0$ gives an optimal basic feasible solution
-- statement:
--   Let $A$ be a real $m\times n$ matrix of rank $m$ with $n\ge m$, $b\in\mathbb{R}^m$, $c\in\mathbb{R}^n$, and let $B$ be a feasible basis of "maximize $c^Tx$ subject to $Ax=b$, $x\ge0$". Let $r=c_N-(c_B^TA_B^{-1}A_N)^T$ be the last row of its simplex tableau $T(B)$. If
--   $$r\le 0,$$
--   then the basic feasible solution of $B$ (the $x$ with $Ax=b$ and $x_j=0$ for all $j\notin B$) is an optimal solution.
--
--   This is the stopping test of the simplex method: when no nonbasic variable has a positive coefficient in the objective row, the current basic feasible solution is optimal.
--
--   **Formalization Note** Indices are 0-based. The basic feasible solution is described by the two properties that determine it ($Ax=b$, zero outside $B$). Optimality is stated against every feasible solution; no supremum is used. The standing assumption of §4.2 is a hypothesis.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, §5.6, p. 67, optimality criterion (boxed, unnumbered)

import Mathlib
import Definitions.Def_MatousekLP_Simplex_Tableau
open Matrix Filter

namespace MatousekLP.Simplex

/-- Optimality criterion (§5.6, p. 67, boxed). If `B` is a feasible basis and the last row of
the simplex tableau `T(B)` has `r ≤ 0`, then the basic feasible solution of `B` is optimal.
Standing assumption of §4.2 (p. 44): `n ≥ m` and `A` has rank `m`. -/
theorem optimality_criterion {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (hmn : m ≤ n) (hrank : A.rank = m) (B : Finset (Fin n)) (hB : B.card = m)
    (hfeas : IsFeasibleBasisOf A b B hB) (hr : tableauR A c B hB ≤ 0) (x : Fin n → ℝ)
    (hx : IsBasicSolutionFor A b B x) :
    MatousekLP.BFS.IsOptimal A b c x := by sorry

end MatousekLP.Simplex
