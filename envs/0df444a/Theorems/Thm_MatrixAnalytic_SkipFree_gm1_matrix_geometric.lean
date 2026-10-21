-- Prove2me | Theorems.Thm_MatrixAnalytic_SkipFree_gm1_matrix_geometric
-- name    : MatrixAnalytic.SkipFree.gm1_matrix_geometric
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:48:44.133836+00:00
-- url     : https://prove2.me/theorems/6e1e11d3-9c3e-4db8-9ceb-bf5effbad609
-- title:
--   Theorem 13.2.3 — matrix-geometric stationary vector π̃_n = π̃₀Kⁿ of a GI/M/1-type chain, K minimal solution of (13.27)
-- statement:
--   Let $\tilde P$ be the transition matrix (13.2) of an irreducible, positive recurrent GI/M/1-type Markov chain with blocks $D_0,D_1,\dots$, $C_0,C_1,\dots$ and stationary probability vector $\tilde\pi=(\tilde\pi_0,\tilde\pi_1,\dots)$, partitioned by levels. Then there is a nonnegative matrix $K$ such that
--   $$\tilde\pi_n=\tilde\pi_0K^n\qquad\text{for all }n\ge0,\tag{13.26}$$
--   where for all $n\ge1$, $K_{ij}$ is the expected number of visits to $(n+1,j)$ before the first return to the level $\ell(n-1)$, given that the chain starts in $(n,i)$. The matrix $K$ is the minimal nonnegative solution of the matrix equation
--   $$K=C_0+KC_1+K^2C_2+\cdots.\tag{13.27}$$
--
--   This is the matrix-geometric property of chains skip-free to the right: the stationary distribution is determined by $\tilde\pi_0$ and the single matrix $K$, characterized as the minimal solution of a matrix power-series equation.
--
--   **Formalization Note** The statement follows the page, including the interpretive clause with the level $\ell(n-1)$; finding F1 of this mission records why that clause, as printed, is expected to be false (the proof's $K=R^{(1)}_{00}$ counts visits before the return to the levels $\ell(0),\dots,\ell(n)$), and the item `gm1_matrix_geometric_corrected` states the corrected clause. "Before the first return to $\ell(n-1)$" is the expected number of visits before the first entrance, after time $0$, into $\ell(n-1)$, as a sum over trajectories. "The stationary probability vector" is rendered as hypotheses: (13.2) is stochastic, irreducible and positive recurrent and $\tilde\pi$ is a stationary probability vector. Minimality is entrywise, over nonnegative real matrices; all products and series are computed in $[0,\infty]$.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 279, Theorem 13.2.3

import Mathlib
import Definitions.Def_MatrixAnalytic_SkipFree_Chain
import Definitions.Def_MatrixAnalytic_SkipFree_QBD
import Definitions.Def_MatrixAnalytic_SkipFree_Passage
import Definitions.Def_MatrixAnalytic_SkipFree_Models

open scoped ENNReal

namespace MatrixAnalytic.SkipFree

/-- Theorem 13.2.3 (p. 279), as printed. For an irreducible, positive recurrent GI/M/1-type chain
(13.2) with stationary probability vector `π̃`, there is a nonnegative matrix `K` with
`π̃_n = π̃₀Kⁿ` (13.26) for all `n ≥ 0`, such that for all `n ≥ 1`, `K_{ij}` is the expected number
of visits to `(n + 1, j)` before the first return to the level `ℓ(n − 1)`, given that the chain
starts in `(n, i)`; and `K` is the minimal nonnegative solution of
`K = C₀ + KC₁ + K²C₂ + ⋯` (13.27). Products and series are computed in `ℝ≥0∞`. -/
theorem gm1_matrix_geometric {ι : Type*} [Countable ι] [DecidableEq ι]
    (D C : ℕ → ι → ι → ℝ) (πt : ℕ × ι → ℝ)
    (hP : IsStochasticC (gm1P D C))
    (hirr : IrreducibleC (gm1P D C))
    (hpos : ∀ x : ℕ × ι, PositiveRecurrent (gm1P D C) x)
    (hπt : IsStationaryC (gm1P D C) πt) :
    ∃ K : ι → ι → ℝ, (∀ i j, 0 ≤ K i j) ∧
      (∀ (n : ℕ) (j : ι), ENNReal.ofReal (πt (n, j)) =
        vecMulE (fun i => ENNReal.ofReal (πt (0, i))) (matPowE (ennMat K) n) j) ∧
      (∀ n : ℕ, 1 ≤ n → ∀ i j,
        expVisitsAvoid (gm1P D C) (level (n - 1)) (n, i) (n + 1, j) = ENNReal.ofReal (K i j)) ∧
      ennMat K = leftSeriesE C (ennMat K) ∧
      ∀ X : ι → ι → ℝ, (∀ i j, 0 ≤ X i j) →
        ennMat X = leftSeriesE C (ennMat X) →
        ∀ i j, K i j ≤ X i j := by sorry

end MatrixAnalytic.SkipFree
