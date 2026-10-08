-- Prove2me | Theorems.Thm_MatousekLP_BFS_basic_iff_positive_columns_linIndep
-- name    : MatousekLP.BFS.basic_iff_positive_columns_linIndep
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T10:54:38.808601+00:00
-- url     : https://prove2.me/theorems/ba1236d6-d664-4ee7-bf75-16a0a111d09b
-- title:
--   Lemma 4.2.1 — basic iff the columns on the positive coordinates are independent
-- statement:
--   Let $A$ be a real $m\times n$ matrix of rank $m$ (so $n\ge m$), let $b\in\mathbb{R}^m$, and consider the linear program in equational form with constraints $Ax=b$, $x\ge 0$. Let $x$ be a feasible solution and let
--
--   $$K=\{\,j\in\{1,\dots,n\} : x_j>0\,\}.$$
--
--   Then $x$ is a basic feasible solution if and only if the columns of $A_K$ (the columns of $A$ indexed by $K$) are linearly independent.
--
--   The lemma removes the choice of the $m$-element set $B$ from the definition of a basic feasible solution: basicness is a property of the support of $x$ alone. It is the step by which the existence proof of Theorem 4.2.3 recognizes a basic feasible solution.
--
--   **Formalization Note** The standing assumption of §4.2 (p. 44), that $A$ has $n\ge m$ columns and rank $m$, is a hypothesis. Indices run over `Fin n`.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, p. 45, Lemma 4.2.1 (standing assumption of §4.2 on p. 44)

import Mathlib
import Definitions.Def_MatousekLP_BFS_EquationalForm
open Matrix

namespace MatousekLP.BFS

/-- Lemma 4.2.1 (p. 45). Standing assumption of §4.2 (p. 44): `A` has `m` rows, `n` columns,
`n ≥ m`, and rank `m`. -/
theorem basic_iff_positive_columns_linIndep {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (hmn : m ≤ n) (hrank : A.rank = m) (x : Fin n → ℝ)
    (hx : IsFeasible A b x) :
    IsBasicFeasible A b x ↔ ColumnsLinIndep A (positiveIndices x) := by sorry

end MatousekLP.BFS
