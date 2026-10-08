-- Prove2me | Theorems.Thm_MatousekLP_BFS_optimal_bfs_exists
-- name    : MatousekLP.BFS.optimal_bfs_exists
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T10:55:02.778089+00:00
-- url     : https://prove2.me/theorems/374e5f24-0a37-46e6-b37a-67388cbc2436
-- title:
--   Theorem 4.2.3 — optimal solutions exist and can be taken basic
-- statement:
--   Let $A$ be a real $m\times n$ matrix of rank $m$ (so $n\ge m$), let $b\in\mathbb{R}^m$ and $c\in\mathbb{R}^n$, and consider the linear program in equational form
--
--   $$\text{maximize } c^{T}x \quad\text{subject to } Ax=b,\ x\ge 0.$$
--
--   1. If there is at least one feasible solution and the objective function $c^{T}x$ is bounded from above on the set of all feasible solutions, then there exists an optimal solution.
--   2. If an optimal solution exists, then there is a basic feasible solution that is optimal.
--
--   Part 1 says that optimal solutions fail to exist only when the program is infeasible or unbounded. Part 2 reduces the search for an optimum to the finitely many basic feasible solutions, which is the principle behind the simplex method.
--
--   **Formalization Note** The standing assumption of §4.2 (p. 44), $n\ge m$ and $\operatorname{rank}A=m$, is a hypothesis. "Optimal" means feasible with $c^{T}y\le c^{T}x$ for every feasible $y$, and "bounded from above" means $c^{T}x\le M$ for some real $M$ and all feasible $x$; no supremum is used. Both parts are stated as one conjunction, as in the book.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, p. 46, Theorem 4.2.3 (standing assumption of §4.2 on p. 44)

import Mathlib
import Definitions.Def_MatousekLP_BFS_EquationalForm
open Matrix

namespace MatousekLP.BFS

/-- Theorem 4.2.3 (p. 46). Standing assumption of §4.2 (p. 44): `A` has `m` rows, `n` columns,
`n ≥ m`, and rank `m`.
(i) A feasible LP whose objective is bounded above on the feasible set has an optimal solution.
(ii) If an optimal solution exists, some basic feasible solution is optimal. -/
theorem optimal_bfs_exists {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (hmn : m ≤ n) (hrank : A.rank = m) :
    ((∃ x, IsFeasible A b x) → IsBoundedAbove A b c → ∃ x, IsOptimal A b c x) ∧
    ((∃ x, IsOptimal A b c x) → ∃ x, IsOptimal A b c x ∧ IsBasicFeasible A b x) := by sorry

end MatousekLP.BFS
