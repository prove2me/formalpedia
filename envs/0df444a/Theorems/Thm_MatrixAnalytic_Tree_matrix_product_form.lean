-- Prove2me | Theorems.Thm_MatrixAnalytic_Tree_matrix_product_form
-- name    : MatrixAnalytic.Tree.matrix_product_form
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:47:59.748369+00:00
-- url     : https://prove2.me/theorems/6ac33e4a-fb82-44d5-85e1-8d8b54ea44ef
-- title:
--   Theorem 14.3.1 — the matrix-product form π{n₁, …, n_k} = π₀ a N R(n₁)⋯R(n_k)
-- statement:
--   Let $Q$ be the generator (14.2) of a tree process with phases $\{1, \dots, m\}$ ($m$ possibly infinite) and data $\boldsymbol a, \boldsymbol d, C, A_i, D_i$, assumed irreducible. Let $N$ be the matrix whose entry $N_{ij}$ is the expected total time spent in the state $(j)$ of the root node $s\{\cdot\}$, starting from $(i)$, before the first visit to the empty state $\emptyset$, and put $R(i) = A_iN$. Assume the process is positive recurrent, let $\pi$ be its stationary probability vector, $\pi_0$ its value at $\emptyset$ and $\pi\{n_1, \dots, n_k\}$ its subvector on the node $s\{n_1, \dots, n_k\}$. Then for all $k \ge 0$ and $1 \le n_1, \dots, n_k \le m$,
--
--   $$\pi\{n_1, n_2, \dots, n_k\} = \pi_0\,\boldsymbol a N R(n_1) R(n_2) \cdots R(n_k).$$
--
--   For $k = 0$ this reads $\pi\{\cdot\} = \pi_0 \boldsymbol a N$. The theorem is the tree analogue of the matrix-geometric form of quasi-birth-and-death processes: the stationary distribution on the infinite tree is determined by the single $m \times m$ matrix $N$.
--
--   **Formalization Note** Phases form an arbitrary countable type; the node $s\{n_1, \dots, n_k\}$ is the list $[n_1, \dots, n_k]$ and the product $R(n_1) \cdots R(n_k)$ is taken left to right. The identity is stated coordinatewise in $[0, \infty]$, with matrix products as sums of nonnegative terms, so it also asserts that the right side is finite. The process is encoded by its jump chain and holding rates; positive recurrence is the return-time notion (finite expected return time), and the stationary vector is a probability vector with $\pi Q = 0$. $N$ is defined at the root node only; that it is the expected-time matrix of every node is part of the content of the theorem.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 290, Theorem 14.3.1

import Mathlib
import Definitions.Def_MatrixAnalytic_Tree_Process
import Definitions.Def_MatrixAnalytic_Tree_Model

open scoped ENNReal

namespace MatrixAnalytic.Tree

/-- Theorem 14.3.1, p. 290: if the tree process is positive recurrent, its stationary probability
vector `π` has the matrix-product form
`π{n₁, …, n_k} = π₀ a N R(n₁) R(n₂) ⋯ R(n_k)` for all `k ≥ 0` and phases `n₁, …, n_k`,
with `R(i) = A_i N`. The node is the list `[n₁, …, n_k]`; the product is taken left to right.
The left side is finite, so the identity also asserts that the right side is finite. -/
theorem matrix_product_form {ι : Type*} [Countable ι] [DecidableEq ι]
    (T : TreeData ι) (hT : IsTreeProcess T)
    (hpr : IsPositiveRecurrentProcess (gen T))
    (π : TreeState ι → ℝ) (hπ : IsStationaryCT (gen T) π) :
    ∀ (ns : List ι) (j : ι),
      ENNReal.ofReal (nodeVec π ns j) =
        (ns.foldl (fun v n => vecMulE v (matRi T n)) (vecMulE (rootVec T π) (matN T))) j := by sorry

end MatrixAnalytic.Tree
