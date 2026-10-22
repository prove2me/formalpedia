-- Prove2me | Theorems.Thm_MatrixAnalytic_SkipFree_H_minimal_solution
-- name    : MatrixAnalytic.SkipFree.H_minimal_solution
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:48:46.577331+00:00
-- url     : https://prove2.me/theorems/bc424d5e-5e40-4679-b71c-679179d3a645
-- title:
--   Theorem 13.1.4 — H is the minimal nonnegative solution of H = Σ_{n≥0} C_n Hⁿ
-- statement:
--   Let $D_0,D_1,\dots$ and $C_0,C_1,\dots$ be the blocks of an M/G/1-type Markov chain with stochastic transition matrix (13.1), and let $H$ be the matrix (13.9) at a level $n\ge1$: for the QBD (13.3)–(13.7) embedding the chain,
--   $$H_{ij}=\mathrm P[\tau<\infty\ \&\ (X_\tau,D_\tau,J_\tau)=(n-1,0,j)\mid(X_0,D_0,J_0)=(n,0,i)],$$
--   $\tau$ the first passage time from $\ell(n)$ to $\ell(n-1)$. Then $H$ is the minimal nonnegative solution of the equation
--   $$H=\sum_{n\ge0}C_nH^n:\tag{13.10}$$
--   $H$ has finite entries, satisfies (13.10), and $H\le Y$ entrywise for every matrix $Y$ with nonnegative real entries satisfying $Y=\sum_{n\ge0}C_nY^n$.
--
--   The first-passage matrix of an M/G/1-type chain, a probabilistic object, is thereby characterized by a matrix power-series equation of the size of one level, the counterpart for chains skip-free to the left of the minimal-solution characterization of $G$ for QBDs (Theorem 8.1.4).
--
--   **Formalization Note** $H$ is defined as a first-passage probability, by a sum over finite trajectories of the QBD (13.3), never as a solution of (13.10). Products and the series $\sum_nC_nY^n$ are computed entrywise in $[0,\infty]$, so the equation is meaningful for every nonnegative $Y$; "minimal" is entrywise (footnote 13, p. 171). The statement is made at every level $n\ge1$.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 273, Theorem 13.1.4, Eq. (13.10)

import Mathlib
import Definitions.Def_MatrixAnalytic_SkipFree_Chain
import Definitions.Def_MatrixAnalytic_SkipFree_QBD
import Definitions.Def_MatrixAnalytic_SkipFree_Passage
import Definitions.Def_MatrixAnalytic_SkipFree_Models

open scoped ENNReal

namespace MatrixAnalytic.SkipFree

/-- Theorem 13.1.4 (p. 273). For an M/G/1-type Markov chain (13.1) and every level `n ≥ 1`, the
matrix `H` (13.9) (first passage from `(n, 0, i)` to `ℓ(n − 1)` in the QBD (13.3), entered at
`(n − 1, 0, j)`) is the minimal nonnegative solution of `H = Σ_{n≥0} C_n Hⁿ` (13.10): its
entries are finite, it solves (13.10), and it lies entrywise below every nonnegative real
solution. Products and series are computed in `ℝ≥0∞`. -/
theorem H_minimal_solution {ι : Type*} [Countable ι] [DecidableEq ι]
    (D C : ℕ → ι → ι → ℝ)
    (hP : IsStochasticC (mg1P D C)) (n : ℕ) (hn : 1 ≤ n) :
    (∀ i j, matH D C n i j ≠ ⊤) ∧
      matH D C n = shiftSeriesE C (matH D C n) 0 ∧
      ∀ Y : ι → ι → ℝ, (∀ i j, 0 ≤ Y i j) →
        ennMat Y = shiftSeriesE C (ennMat Y) 0 →
        ∀ i j, matH D C n i j ≤ ennMat Y i j := by sorry

end MatrixAnalytic.SkipFree
