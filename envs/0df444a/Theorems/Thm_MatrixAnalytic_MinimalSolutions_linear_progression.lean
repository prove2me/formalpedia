-- Prove2me | Theorems.Thm_MatrixAnalytic_MinimalSolutions_linear_progression
-- name    : MatrixAnalytic.MinimalSolutions.linear_progression
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:44:36.088453+00:00
-- url     : https://prove2.me/theorems/fa3afc27-cdf4-40f5-bef3-3977e7265c32
-- title:
--   Theorem 8.1.1 — U(k), G(k) satisfy (8.7)–(8.9), increase and converge to U and G
-- statement:
--   Let $X$ be an irreducible homogeneous QBD with transition matrix (8.1), blocks $B, A_0, A_1, A_2$ indexed by a countable (finite or infinite) set of phases. Let $U$ and $G$ be the first-return and first-passage matrices (8.4), (8.3), and for $k\ge1$ let $U(k)$ and $G(k)$ be the taboo matrices
--
--   $$U(k) = \mathrm P[\gamma(1)<\gamma(0)\ \&\ \gamma(1)<\gamma(k+1)\ \&\ X_{\gamma(1)}\mid X_0\in\ell(1)],\qquad G(k) = \mathrm P[\gamma(0)<\gamma(k+1)\ \&\ X_{\gamma(0)}\mid X_0\in\ell(1)].$$
--
--   Then, with $G(0)=0$ (8.7):
--
--   1. $U(1) = A_1$ and $U(k+1) = A_1 + A_0G(k)$ for $k\ge1$ (8.8);
--   2. for $k\ge1$ the series $\sum_{\nu\ge0}U(k)^\nu = (I-U(k))^{-1}$ converges and $G(k) = (I-U(k))^{-1}A_2$ (8.9);
--   3. both sequences are monotonically increasing, $U(k)\le U(k+1)$ and $G(k)\le G(k+1)$ entrywise;
--   4. $U(k)\to U$ and $G(k)\to G$ entrywise as $k\to\infty$.
--
--   This is the basis of the linear progression algorithm (Figure 8.1), and it identifies the limits of the iteration with the probabilistic matrices rather than with some other solution of (8.5)–(8.6).
--
--   **Formalization Note** All matrices are computed with entries in $[0,\infty]$; $(I-M)^{-1}$ is the series $\sum_\nu M^\nu$, the book's convention for matrices of infinite order, and its convergence is part of the conclusion. The convention $G(0)=0$ is built in by stating (8.8) separately for $k=1$.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, pp. 168–169, Theorem 8.1.1

import Mathlib
import Definitions.Def_MatrixAnalytic_MinimalSolutions_Chain
import Definitions.Def_MatrixAnalytic_MinimalSolutions_QBD
import Definitions.Def_MatrixAnalytic_MinimalSolutions_Passage

open scoped ENNReal

namespace MatrixAnalytic.MinimalSolutions

/-- Theorem 8.1.1 (pp. 168–169). For an irreducible QBD (8.1), the taboo first-passage matrices
`U(k)` (8.10) and `G(k)` (8.11), `k ≥ 1`, satisfy (8.7)–(8.9) — with `G(0) = 0`, so that
`U(1) = A₁`, `U(k + 1) = A₁ + A₀G(k)` and `G(k) = (I − U(k))⁻¹A₂ := Σ_ν U(k)^ν A₂`, the series
converging — are monotonically increasing, and converge entrywise to `U` (8.4) and `G` (8.3).
Products and series are computed in `ℝ≥0∞`. -/
theorem linear_progression {ι : Type*} [Countable ι] [DecidableEq ι]
    (B A₀ A₁ A₂ : ι → ι → ℝ)
    (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂)) :
    matUk (qbdP B A₀ A₁ A₂) 1 = ennMat A₁ ∧
      (∀ k : ℕ, 1 ≤ k →
        matUk (qbdP B A₀ A₁ A₂) (k + 1) =
          ennMat A₁ + matMulE (ennMat A₀) (matGk (qbdP B A₀ A₁ A₂) k)) ∧
      (∀ k : ℕ, 1 ≤ k →
        (∀ i j, seriesInvE (matUk (qbdP B A₀ A₁ A₂) k) i j ≠ ⊤) ∧
          matGk (qbdP B A₀ A₁ A₂) k =
            matMulE (seriesInvE (matUk (qbdP B A₀ A₁ A₂) k)) (ennMat A₂)) ∧
      (∀ k : ℕ, 1 ≤ k → ∀ i j,
        matUk (qbdP B A₀ A₁ A₂) k i j ≤ matUk (qbdP B A₀ A₁ A₂) (k + 1) i j ∧
          matGk (qbdP B A₀ A₁ A₂) k i j ≤ matGk (qbdP B A₀ A₁ A₂) (k + 1) i j) ∧
      (∀ i j, Filter.Tendsto (fun k => matUk (qbdP B A₀ A₁ A₂) k i j) Filter.atTop
        (nhds (matU (qbdP B A₀ A₁ A₂) i j))) ∧
      (∀ i j, Filter.Tendsto (fun k => matGk (qbdP B A₀ A₁ A₂) k i j) Filter.atTop
        (nhds (matG (qbdP B A₀ A₁ A₂) i j))) := by sorry

end MatrixAnalytic.MinimalSolutions
