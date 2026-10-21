-- Prove2me | Theorems.Thm_MatrixAnalytic_MinimalSolutions_minimal_solutions
-- name    : MatrixAnalytic.MinimalSolutions.minimal_solutions
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:44:43.470669+00:00
-- url     : https://prove2.me/theorems/dfc9dab6-aedd-4f4b-902b-0a1d52c91f85
-- title:
--   Theorem 8.1.4 — U, R, G as minimal nonnegative solutions of (8.13)–(8.16)
-- statement:
--   Let $X$ be an irreducible homogeneous QBD with transition matrix (8.1), with blocks $B, A_0, A_1, A_2$ indexed by a countable (finite or infinite) set of phases. Let $U$ and $G$ be the first-return and first-passage matrices (8.4), (8.3), and let $R$ be the matrix of Theorem 6.2.1: $R_{ij}$ is the expected number of visits to $(1,j)$ before the first return to $\ell(0)$, starting from $(0,i)$. A solution $X$ of a matrix equation is *minimal* in a set of nonnegative matrices if $X_{ij}\le Y_{ij}$ for all $i,j$ and every solution $Y$ in that set. Then:
--
--   1. $U$ and $R$ are the minimal solutions of the system
--   $$X = A_1 + ZA_2,\qquad Z = A_0\sum_{\nu\ge0}X^\nu \tag{8.13}$$
--   in the set of nonnegative matrices such that the series converges;
--   2. $U$ is the minimal solution of the equation
--   $$X = A_1 + A_0\sum_{\nu\ge0}X^\nu A_2 \tag{8.14}$$
--   in the set of nonnegative matrices such that the series converges;
--   3. $G$ is the minimal solution of the equation
--   $$Y = A_2 + A_1Y + A_0Y^2 \tag{8.15}$$
--   in the set of nonnegative matrices;
--   4. $R$ is the minimal solution of the equation
--   $$Z = A_0 + ZA_1 + Z^2A_2 \tag{8.16}$$
--   in the set of nonnegative matrices.
--
--   In each case the probabilistic matrix itself belongs to the set (finite entries, and the series converging where one appears) and solves the equation. The theorem turns each of the quadratic and series equations satisfied by $U$, $G$ and $R$ into a complete characterization, and so justifies algorithms built on any of them.
--
--   **Formalization Note** $U$, $G$ and $R$ are defined as probabilities and expected numbers of visits (sums over finite taboo trajectories of products of transition probabilities), not as solutions of these equations, so minimality is a genuine statement about the QBD. Products and series are computed entrywise in $[0,\infty]$; the candidate solutions range over real matrices with nonnegative entries, and "the series converges" means that every entry of $\sum_\nu X^\nu$ is finite. No recurrence assumption is made, as in the book's Chapter 8.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 172, Theorem 8.1.4 (minimality as in footnote 13, p. 171)

import Mathlib
import Definitions.Def_MatrixAnalytic_MinimalSolutions_Chain
import Definitions.Def_MatrixAnalytic_MinimalSolutions_QBD
import Definitions.Def_MatrixAnalytic_MinimalSolutions_Passage

open scoped ENNReal

namespace MatrixAnalytic.MinimalSolutions

/-- Theorem 8.1.4 (p. 172). For an irreducible QBD (8.1), with `U` (8.4), `G` (8.3) and `R` the
expected-visits matrix of Theorem 6.2.1, and `Σ_ν X^ν` the book's `(I − X)⁻¹`:
1. `(U, R)` is the minimal solution of (8.13) `X = A₁ + ZA₂`, `Z = A₀ Σ_ν X^ν` among pairs of
   nonnegative real matrices for which the series converges;
2. `U` is the minimal solution of (8.14) `X = A₁ + A₀ Σ_ν X^ν A₂` among nonnegative real
   matrices for which the series converges;
3. `G` is the minimal nonnegative solution of (8.15) `Y = A₂ + A₁Y + A₀Y²`;
4. `R` is the minimal nonnegative solution of (8.16) `Z = A₀ + ZA₁ + Z²A₂`.
"Minimal" is footnote 13 (p. 171): entrywise below every nonnegative solution. Each of `U, G, R`
is itself an admissible solution (finite entries, convergent series). Products and series are
computed in `ℝ≥0∞`. -/
theorem minimal_solutions {ι : Type*} [Countable ι] [DecidableEq ι]
    (B A₀ A₁ A₂ : ι → ι → ℝ)
    (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂)) :
    -- (8.13): `(U, R)` solves the system, with convergent series, and is minimal
    ((∀ i j, seriesInvE (matU (qbdP B A₀ A₁ A₂)) i j ≠ ⊤) ∧
      (∀ i j, matR (qbdP B A₀ A₁ A₂) i j ≠ ⊤) ∧
      matU (qbdP B A₀ A₁ A₂) = ennMat A₁ + matMulE (matR (qbdP B A₀ A₁ A₂)) (ennMat A₂) ∧
      matR (qbdP B A₀ A₁ A₂) = matMulE (ennMat A₀) (seriesInvE (matU (qbdP B A₀ A₁ A₂))) ∧
      ∀ X Z : ι → ι → ℝ, (∀ i j, 0 ≤ X i j) → (∀ i j, 0 ≤ Z i j) →
        (∀ i j, seriesInvE (ennMat X) i j ≠ ⊤) →
        ennMat X = ennMat A₁ + matMulE (ennMat Z) (ennMat A₂) →
        ennMat Z = matMulE (ennMat A₀) (seriesInvE (ennMat X)) →
        ∀ i j, matU (qbdP B A₀ A₁ A₂) i j ≤ ennMat X i j ∧
          matR (qbdP B A₀ A₁ A₂) i j ≤ ennMat Z i j) ∧
    -- (8.14): `U` solves the equation, with convergent series, and is minimal
    (matU (qbdP B A₀ A₁ A₂) = ennMat A₁ +
        matMulE (matMulE (ennMat A₀) (seriesInvE (matU (qbdP B A₀ A₁ A₂)))) (ennMat A₂) ∧
      ∀ X : ι → ι → ℝ, (∀ i j, 0 ≤ X i j) →
        (∀ i j, seriesInvE (ennMat X) i j ≠ ⊤) →
        ennMat X = ennMat A₁ + matMulE (matMulE (ennMat A₀) (seriesInvE (ennMat X))) (ennMat A₂) →
        ∀ i j, matU (qbdP B A₀ A₁ A₂) i j ≤ ennMat X i j) ∧
    -- (8.15): `G` is a nonnegative solution and is minimal
    ((∀ i j, matG (qbdP B A₀ A₁ A₂) i j ≠ ⊤) ∧
      matG (qbdP B A₀ A₁ A₂) = ennMat A₂ + matMulE (ennMat A₁) (matG (qbdP B A₀ A₁ A₂)) +
        matMulE (ennMat A₀) (matMulE (matG (qbdP B A₀ A₁ A₂)) (matG (qbdP B A₀ A₁ A₂))) ∧
      ∀ Y : ι → ι → ℝ, (∀ i j, 0 ≤ Y i j) →
        ennMat Y = ennMat A₂ + matMulE (ennMat A₁) (ennMat Y) +
          matMulE (ennMat A₀) (matMulE (ennMat Y) (ennMat Y)) →
        ∀ i j, matG (qbdP B A₀ A₁ A₂) i j ≤ ennMat Y i j) ∧
    -- (8.16): `R` is a nonnegative solution and is minimal
    ((∀ i j, matR (qbdP B A₀ A₁ A₂) i j ≠ ⊤) ∧
      matR (qbdP B A₀ A₁ A₂) = ennMat A₀ + matMulE (matR (qbdP B A₀ A₁ A₂)) (ennMat A₁) +
        matMulE (matMulE (matR (qbdP B A₀ A₁ A₂)) (matR (qbdP B A₀ A₁ A₂))) (ennMat A₂) ∧
      ∀ Z : ι → ι → ℝ, (∀ i j, 0 ≤ Z i j) →
        ennMat Z = ennMat A₀ + matMulE (ennMat Z) (ennMat A₁) +
          matMulE (matMulE (ennMat Z) (ennMat Z)) (ennMat A₂) →
        ∀ i j, matR (qbdP B A₀ A₁ A₂) i j ≤ ennMat Z i j) := by sorry

end MatrixAnalytic.MinimalSolutions
