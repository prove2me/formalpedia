-- Prove2me | Theorems.Thm_MatousekLP_BFS_bfs_unique_of_basis
-- name    : MatousekLP.BFS.bfs_unique_of_basis
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T10:54:49.240001+00:00
-- url     : https://prove2.me/theorems/1051051d-041e-4850-b3d3-20dad0a8c109
-- title:
--   Proposition 4.2.2 — a basic feasible solution is determined by its basis
-- statement:
--   Let $A$ be a real $m\times n$ matrix of rank $m$ (so $n\ge m$), let $b\in\mathbb{R}^m$, and let $B\subseteq\{1,\dots,n\}$ be an $m$-element set such that the columns of $A_B$ are linearly independent. If $x$ and $y$ are feasible solutions of $Ax=b$, $x\ge0$ with
--
--   $$x_j=0\ \text{ and }\ y_j=0\qquad\text{for all } j\notin B,$$
--
--   then $x=y$. That is, there is at most one feasible solution vanishing outside $B$.
--
--   The proposition shows that there are at most $\binom{n}{m}$ basic feasible solutions and justifies calling a set $B$ that determines one a feasible basis.
--
--   **Formalization Note** The standing assumption of §4.2 (p. 44), $n\ge m$ and $\operatorname{rank}A=m$, is kept as a hypothesis, as on the page.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, p. 45, Proposition 4.2.2 (standing assumption of §4.2 on p. 44)

import Mathlib
import Definitions.Def_MatousekLP_BFS_EquationalForm
open Matrix

namespace MatousekLP.BFS

/-- Proposition 4.2.2 (p. 45). Standing assumption of §4.2 (p. 44): `A` has `m` rows, `n`
columns, `n ≥ m`, and rank `m`. -/
theorem bfs_unique_of_basis {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (hmn : m ≤ n) (hrank : A.rank = m) (B : Finset (Fin n))
    (hB : IsBasis A B) (x y : Fin n → ℝ)
    (hx : IsFeasible A b x) (hxB : ∀ j, j ∉ B → x j = 0)
    (hy : IsFeasible A b y) (hyB : ∀ j, j ∉ B → y j = 0) :
    x = y := by sorry

end MatousekLP.BFS
