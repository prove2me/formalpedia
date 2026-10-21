-- Prove2me | Theorems.Thm_MatrixAnalytic_MinimalSolutions_improved_algorithm
-- name    : MatrixAnalytic.MinimalSolutions.improved_algorithm
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:44:27.818721+00:00
-- url     : https://prove2.me/theorems/bcabed76-add0-4610-b3c7-311470ee69cd
-- title:
--   Theorem 8.3.1 — the iteration from Ḡ(0) = I is well defined, stochastic, and converges to U and G
-- statement:
--   Let $X$ be an irreducible homogeneous QBD with transition matrix (8.1), with a finite number $m$ of phases, and assume that the QBD is recurrent. Define
--
--   $$\bar G(0) = I,\qquad \bar U(k) = A_1 + A_0\bar G(k-1),\qquad \bar G(k) = (I - \bar U(k))^{-1}A_2 \quad\text{for } k\ge1. \tag{8.29–8.31}$$
--
--   Then:
--
--   1. $I - \bar U(k)$ is nonsingular for every $k\ge1$, so the sequences are well defined;
--   2. $\bar U(k)$ is substochastic and $\bar G(k)$ is stochastic for all $k$;
--   3. $\lim_{k\to\infty}\bar U(k) = U$ and $\lim_{k\to\infty}\bar G(k) = G$, with $U$, $G$ the matrices (8.4), (8.3);
--   4. $\bar G(k)\ge G(k)$ and $\bar U(k)\ge U(k)$ for all $k\ge1$, with $G(k)$, $U(k)$ the taboo matrices (8.11), (8.10).
--
--   Starting from a stochastic matrix instead of $0$ speeds up the linear progression algorithm in the recurrent case.
--
--   **Formalization Note** The inverse is the matrix inverse of a finite real matrix; its existence is item 1 of the conclusion, not a hypothesis. "Substochastic" means nonnegative entries and row sums at most $1$; "stochastic" means nonnegative entries and row sums equal to $1$. Convergence is entrywise, comparing $\bar U(k)$, $\bar G(k)$ (read in $[0,\infty]$) with the probabilistic matrices. Item 4 is stated for $k\ge1$, the range on which $U(k)$, $G(k)$ are defined; at $k=0$ the book's $G(0)=0\le I$ is immediate.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, pp. 179–180, Theorem 8.3.1

import Mathlib
import Definitions.Def_MatrixAnalytic_MinimalSolutions_Chain
import Definitions.Def_MatrixAnalytic_MinimalSolutions_QBD
import Definitions.Def_MatrixAnalytic_MinimalSolutions_Passage
import Definitions.Def_MatrixAnalytic_MinimalSolutions_Improved

open scoped ENNReal

namespace MatrixAnalytic.MinimalSolutions

/-- Theorem 8.3.1 (pp. 179–180). For an irreducible recurrent QBD (8.1) with finitely many
phases, the sequences `Ḡ(0) = I`, `Ū(k) = A₁ + A₀Ḡ(k − 1)`, `Ḡ(k) = (I − Ū(k))⁻¹A₂` (`k ≥ 1`) are
well defined (`I − Ū(k)` is nonsingular), `Ū(k)` is substochastic (nonnegative, row sums `≤ 1`)
and `Ḡ(k)` is stochastic for all `k`, `Ū(k) → U` and `Ḡ(k) → G` entrywise, and
`Ḡ(k) ≥ G(k)`, `Ū(k) ≥ U(k)` for all `k ≥ 1`, with `U, G, U(k), G(k)` the probabilistic matrices
(8.4), (8.3), (8.10), (8.11). -/
theorem improved_algorithm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B A₀ A₁ A₂ : Matrix ι ι ℝ)
    (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂))
    (hrec : ∀ x : ℕ × ι, Recurrent (qbdP B A₀ A₁ A₂) x) :
    (∀ k : ℕ, 1 ≤ k → IsUnit (1 - Ubar A₀ A₁ A₂ k)) ∧
      (∀ k : ℕ, 1 ≤ k →
        (∀ i j, 0 ≤ Ubar A₀ A₁ A₂ k i j) ∧ ∀ i, ∑ j, Ubar A₀ A₁ A₂ k i j ≤ 1) ∧
      (∀ k : ℕ, (∀ i j, 0 ≤ Gbar A₀ A₁ A₂ k i j) ∧ ∀ i, ∑ j, Gbar A₀ A₁ A₂ k i j = 1) ∧
      (∀ i j, Filter.Tendsto (fun k => ENNReal.ofReal (Ubar A₀ A₁ A₂ k i j)) Filter.atTop
        (nhds (matU (qbdP B A₀ A₁ A₂) i j))) ∧
      (∀ i j, Filter.Tendsto (fun k => ENNReal.ofReal (Gbar A₀ A₁ A₂ k i j)) Filter.atTop
        (nhds (matG (qbdP B A₀ A₁ A₂) i j))) ∧
      (∀ k : ℕ, 1 ≤ k → ∀ i j,
        matGk (qbdP B A₀ A₁ A₂) k i j ≤ ENNReal.ofReal (Gbar A₀ A₁ A₂ k i j) ∧
          matUk (qbdP B A₀ A₁ A₂) k i j ≤ ENNReal.ofReal (Ubar A₀ A₁ A₂ k i j)) := by sorry

end MatrixAnalytic.MinimalSolutions
