-- Prove2me | Theorems.Thm_MatousekLP_BFS_exists_bfs_ge
-- name    : MatousekLP.BFS.exists_bfs_ge
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T10:54:56.278404+00:00
-- url     : https://prove2.me/theorems/c0acf055-f128-41b4-97d0-0b91aa6870d1
-- title:
--   Proof of Theorem 4.2.3 — every feasible solution is dominated by a basic feasible solution
-- statement:
--   Let $A$ be a real $m\times n$ matrix of rank $m$ (so $n\ge m$), let $b\in\mathbb{R}^m$ and $c\in\mathbb{R}^n$, and consider
--
--   $$\text{maximize } c^{T}x \quad\text{subject to } Ax=b,\ x\ge 0.$$
--
--   Suppose the objective function is bounded from above on the set of feasible solutions. Then for every feasible solution $x_0$ there is a basic feasible solution $\tilde x$ with
--
--   $$c^{T}\tilde x\ \ge\ c^{T}x_0.$$
--
--   This is the statement the book proves in order to obtain Theorem 4.2.3: since there are finitely many basic feasible solutions, the best of them is optimal.
--
--   **Formalization Note** The standing assumption of §4.2 (p. 44), $n\ge m$ and $\operatorname{rank}A=m$, is a hypothesis. Boundedness is the existence of a real $M$ with $c^{T}x\le M$ for all feasible $x$.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, p. 47, statement proved in the proof of Theorem 4.2.3 (standing assumption of §4.2 on p. 44)

import Mathlib
import Definitions.Def_MatousekLP_BFS_EquationalForm
open Matrix

namespace MatousekLP.BFS

/-- The statement proved inside the proof of Theorem 4.2.3 (p. 47). Standing assumption of §4.2
(p. 44): `A` has `m` rows, `n` columns, `n ≥ m`, and rank `m`. -/
theorem exists_bfs_ge {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (hmn : m ≤ n) (hrank : A.rank = m)
    (hbdd : IsBoundedAbove A b c) (x₀ : Fin n → ℝ) (hx₀ : IsFeasible A b x₀) :
    ∃ x : Fin n → ℝ, IsBasicFeasible A b x ∧ c ⬝ᵥ x₀ ≤ c ⬝ᵥ x := by sorry

end MatousekLP.BFS
