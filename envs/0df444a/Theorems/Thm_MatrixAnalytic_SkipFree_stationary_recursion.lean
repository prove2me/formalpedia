-- Prove2me | Theorems.Thm_MatrixAnalytic_SkipFree_stationary_recursion
-- name    : MatrixAnalytic.SkipFree.stationary_recursion
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:48:43.731719+00:00
-- url     : https://prove2.me/theorems/9a87fd8d-931d-4923-bf4e-a8bef92a2527
-- title:
--   Theorem 13.1.5 — the recursion (13.12) for the stationary vector of an M/G/1-type chain
-- statement:
--   Let $\tilde P$ be the transition matrix (13.1) of an irreducible, positive recurrent M/G/1-type Markov chain with blocks $D_0,D_1,\dots$, $C_0,C_1,\dots$ and stationary probability vector $\tilde\pi=(\tilde\pi_0,\tilde\pi_1,\dots)$, partitioned by levels. Let $H$ be the matrix (13.9) and define, for $n\ge1$,
--   $$\bar C_n=\sum_{i\ge0}C_{n+i}H^i,\qquad\bar D_n=\sum_{i\ge0}D_{n+i}H^i.$$
--   Then $I-\bar C_1$ is nonsingular, in the sense that $(I-\bar C_1)^{-1}=\sum_{\nu\ge0}\bar C_1^{\,\nu}$ has finite entries, and for every $n\ge1$
--   $$\tilde\pi_n=\Big(\tilde\pi_0\bar D_n+\sum_{1\le j\le n-1}\tilde\pi_j\bar C_{n-j+1}\Big)(I-\bar C_1)^{-1},$$
--   the sum being empty for $n=1$.
--
--   This is the recursive scheme that replaces, for chains skip-free to the left, the matrix-geometric form of the stationary distribution of a QBD: $\tilde\pi_0$ determines all the other $\tilde\pi_n$.
--
--   **Formalization Note** $H$ is taken at level $1$ (from $(1,0,i)$ to $\ell(0)$ in the QBD (13.3)). The inverse $(I-\bar C_1)^{-1}$ is the book's convention $\sum_{\nu\ge0}\bar C_1^{\,\nu}$ (p. 109), and its finiteness, which the proof asserts ("$I-\bar C_1$ is nonsingular"), is part of the conclusion. All products and series are computed in $[0,\infty]$. The book's remark that "for $n=0$, the empty sum in (13.12) is taken to be zero" concerns $n=1$ (the sum over $1\le j\le n-1$ is empty exactly then; $\bar D_n$ is defined for $n\ge1$); the statement is made for $n\ge1$ as the proof does.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, pp. 273–274, Theorem 13.1.5, Eq. (13.12)

import Mathlib
import Definitions.Def_MatrixAnalytic_SkipFree_Chain
import Definitions.Def_MatrixAnalytic_SkipFree_QBD
import Definitions.Def_MatrixAnalytic_SkipFree_Passage
import Definitions.Def_MatrixAnalytic_SkipFree_Models

open scoped ENNReal

namespace MatrixAnalytic.SkipFree

/-- Theorem 13.1.5 (pp. 273–274). Let `π̃` be the stationary probability vector of an irreducible,
positive recurrent M/G/1-type chain (13.1), `H` the matrix (13.9) (taken at level `1`), and
`C̄_n = Σ_{i≥0} C_{n+i} Hⁱ`, `D̄_n = Σ_{i≥0} D_{n+i} Hⁱ`. With the book's convention
`(I − C̄₁)⁻¹ := Σ_{ν≥0} C̄₁^ν` (p. 109), whose entries are finite (`I − C̄₁` is nonsingular),
`π̃_n = (π̃₀ D̄_n + Σ_{1≤j≤n−1} π̃_j C̄_{n−j+1}) (I − C̄₁)⁻¹` (13.12) for every `n ≥ 1`
(the sum is empty for `n = 1`). Products and series are computed in `ℝ≥0∞`. -/
theorem stationary_recursion {ι : Type*} [Countable ι] [DecidableEq ι]
    (D C : ℕ → ι → ι → ℝ) (πt : ℕ × ι → ℝ)
    (hP : IsStochasticC (mg1P D C))
    (hirr : IrreducibleC (mg1P D C))
    (hpos : ∀ x : ℕ × ι, PositiveRecurrent (mg1P D C) x)
    (hπt : IsStationaryC (mg1P D C) πt) :
    (∀ i j, seriesInvE (shiftSeriesE C (matH D C 1) 1) i j ≠ ⊤) ∧
      ∀ n : ℕ, 1 ≤ n → ∀ j : ι,
        ENNReal.ofReal (πt (n, j)) =
          vecMulE
            (vecMulE (fun i => ENNReal.ofReal (πt (0, i))) (shiftSeriesE D (matH D C 1) n) +
              ∑ l ∈ Finset.Ico 1 n,
                vecMulE (fun i => ENNReal.ofReal (πt (l, i)))
                  (shiftSeriesE C (matH D C 1) (n - l + 1)))
            (seriesInvE (shiftSeriesE C (matH D C 1) 1)) j := by sorry

end MatrixAnalytic.SkipFree
