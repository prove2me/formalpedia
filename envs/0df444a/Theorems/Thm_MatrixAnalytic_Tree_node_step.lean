-- Prove2me | Theorems.Thm_MatrixAnalytic_Tree_node_step
-- name    : MatrixAnalytic.Tree.node_step
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:47:59.78584+00:00
-- url     : https://prove2.me/theorems/336c1ff1-abd2-4ae9-804d-824f5c6e1874
-- title:
--   Eq. (14.5) — π{n, j} = π{n} A_j N
-- statement:
--   Let $Q$ be the generator of a tree process with phases $\{1, \dots, m\}$ and data $\boldsymbol a, \boldsymbol d, C, A_j, D_j$ (Chapter 14 of Latouche & Ramaswami), assumed irreducible. Let $N$ be the matrix of expected times spent in the root node $s\{\cdot\}$ before the first visit to the empty state $\emptyset$. Assume the process is positive recurrent and let $\pi$ be its stationary probability vector. Then for every node $s\{\boldsymbol n\}$, $\boldsymbol n = (n_1, \dots, n_k)$ with $k \ge 0$, and every phase $j$,
--
--   $$\pi\{\boldsymbol n, j\} = \pi\{\boldsymbol n\}\, A_j N .$$
--
--   This is the one-step relation from which the matrix-product form (14.4) follows: the stationary subvector of a child node is that of its parent multiplied by the rate matrix into that child and by the expected-time matrix $N$, which is the same for every node.
--
--   **Formalization Note** The identity is stated coordinatewise in $[0, \infty]$: the left side is $\pi\{\boldsymbol n, j\}_i$ read as an extended real, and the right side is $\sum_k \sum_l \pi\{\boldsymbol n\}_l [A_j]_{lk} N_{ki}$, a sum of nonnegative terms. The identity therefore also asserts that the right side is finite. $N$ is defined at the root node; that the expected-time matrix of every other node equals it is part of what the statement asserts.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 290, Eq. (14.5)

import Mathlib
import Definitions.Def_MatrixAnalytic_Tree_Process
import Definitions.Def_MatrixAnalytic_Tree_Model

open scoped ENNReal

namespace MatrixAnalytic.Tree

/-- Eq. (14.5), p. 290: for a positive recurrent tree process with stationary probability vector
`π`, the subvector of every node `s{n, j}` is that of its parent `s{n}` times `A_j N`:
`π{n, j} = π{n} A_j N`. The left side is finite, so the identity also asserts that the right
side is finite. -/
theorem node_step {ι : Type*} [Countable ι] [DecidableEq ι]
    (T : TreeData ι) (hT : IsTreeProcess T)
    (hpr : IsPositiveRecurrentProcess (gen T))
    (π : TreeState ι → ℝ) (hπ : IsStationaryCT (gen T) π) :
    ∀ (n : List ι) (j i : ι),
      ENNReal.ofReal (nodeVec π (n ++ [j]) i) =
        vecMulE (vecMulE (fun k => ENNReal.ofReal (nodeVec π n k)) (ennMat (T.A j))) (matN T) i := by sorry

end MatrixAnalytic.Tree
