-- Prove2me | Theorems.Thm_MatousekLP_BFS_vertex_iff_bfs
-- name    : MatousekLP.BFS.vertex_iff_bfs
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T10:55:15.80142+00:00
-- url     : https://prove2.me/theorems/53fce141-060f-4618-9c8f-59e7290a14f9
-- title:
--   Theorem 4.4.1 — vertices are exactly the basic feasible solutions
-- statement:
--   Let $A$ be a real $m\times n$ matrix of rank $m$ with $n\ge m$ and $n\ge 1$, let $b\in\mathbb{R}^m$, and let
--
--   $$P=\{x\in\mathbb{R}^n : Ax=b,\ x\ge 0\}$$
--
--   be the set of feasible solutions of the linear program in equational form. For a point $v\in P$ the following are equivalent:
--
--   1. $v$ is a vertex of $P$: there is a nonzero $c\in\mathbb{R}^n$ with $c^{T}v>c^{T}y$ for all $y\in P\setminus\{v\}$;
--   2. $v$ is a basic feasible solution of the linear program.
--
--   The theorem identifies the algebraic notion used by the simplex method with the geometric "corners" of the feasible polyhedron.
--
--   **Formalization Note** The standing assumption of §4.2 (p. 44), $n\ge m$ and $\operatorname{rank}A=m$, is a hypothesis. The hypothesis $n\ge 1$ is added: for $n=0$ there is no nonzero $c\in\mathbb{R}^0$, so the unique feasible point $0$ is basic (with $B=\emptyset$) but not a vertex in the book's sense, and the equivalence fails; the book tacitly works with $n\ge 1$. "Vertex" is the book's unique-maximizer definition, not Mathlib's extreme points.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, p. 54, Theorem 4.4.1 (vertex definition p. 53; standing assumption of §4.2 on p. 44)

import Mathlib
import Definitions.Def_MatousekLP_BFS_EquationalForm
open Matrix

namespace MatousekLP.BFS

/-- Theorem 4.4.1 (p. 54). Standing assumption of §4.2 (p. 44): `A` has `m` rows, `n` columns,
`n ≥ m`, and rank `m`. The book's vertex definition asks for a nonzero `c ∈ ℝⁿ`, which does
not exist for `n = 0`; the book tacitly has `n ≥ 1`, recorded as `hn`. -/
theorem vertex_iff_bfs {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (hn : 0 < n) (hmn : m ≤ n) (hrank : A.rank = m) (v : Fin n → ℝ)
    (hv : v ∈ feasibleSet A b) :
    IsVertex (feasibleSet A b) v ↔ IsBasicFeasible A b v := by sorry

end MatousekLP.BFS
