-- Prove2me | Theorems.Thm_MatrixAnalytic_MinimalSolutions_UG_minimal
-- name    : MatrixAnalytic.MinimalSolutions.UG_minimal
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:44:37.328647+00:00
-- url     : https://prove2.me/theorems/dabf9062-eb7f-410c-9453-fe3c8f523d93
-- title:
--   Theorem 8.1.3 — (U, G) is the minimal solution of X = A₁ + A₀Y, Y = Σ X^ν A₂
-- statement:
--   Let $X$ be an irreducible homogeneous QBD with transition matrix (8.1), with a countable (finite or infinite) set of phases, and let $U$, $G$ be the matrices (8.4), (8.3). Consider the system
--
--   $$X = A_1 + A_0Y,\qquad Y = \sum_{\nu\ge0}X^\nu A_2 \tag{8.12}$$
--
--   in the set of pairs $(X,Y)$ of nonnegative real matrices such that the series $\sum_{\nu\ge0}X^\nu$ converges. Then $(U,G)$ belongs to this set and solves (8.12), and it is the minimal solution: for every such solution $(X,Y)$, $U_{ij}\le X_{ij}$ and $G_{ij}\le Y_{ij}$ for all $i,j$.
--
--   The theorem shows that the equations (8.5)–(8.6) characterize $U$ and $G$ completely, subject to minimality.
--
--   **Formalization Note** Products and series are computed entrywise in $[0,\infty]$; a candidate $(X,Y)$ is a pair of real matrices with nonnegative entries, and the equations are asserted for them read in $[0,\infty]$, so a solution has finite products. The finiteness of the entries of $G$ is stated explicitly.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 171, Theorem 8.1.3 (minimality as in footnote 13)

import Mathlib
import Definitions.Def_MatrixAnalytic_MinimalSolutions_Chain
import Definitions.Def_MatrixAnalytic_MinimalSolutions_QBD
import Definitions.Def_MatrixAnalytic_MinimalSolutions_Passage

open scoped ENNReal

namespace MatrixAnalytic.MinimalSolutions

/-- Theorem 8.1.3 (p. 171). For an irreducible QBD (8.1), the pair `(U, G)` of (8.4), (8.3) is the
minimal solution of the system (8.12) `X = A₁ + A₀Y`, `Y = Σ_{ν ≥ 0} X^ν A₂` in the set of pairs
of nonnegative real matrices for which the series `Σ_ν X^ν` converges: `(U, G)` is such a pair
(finite entries, convergent series) and `U ≤ X`, `G ≤ Y` entrywise for every such solution
`(X, Y)`. Products and series are computed in `ℝ≥0∞`. -/
theorem UG_minimal {ι : Type*} [Countable ι] [DecidableEq ι]
    (B A₀ A₁ A₂ : ι → ι → ℝ)
    (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂)) :
    (∀ i j, matG (qbdP B A₀ A₁ A₂) i j ≠ ⊤) ∧
      (∀ i j, seriesInvE (matU (qbdP B A₀ A₁ A₂)) i j ≠ ⊤) ∧
      matU (qbdP B A₀ A₁ A₂) = ennMat A₁ + matMulE (ennMat A₀) (matG (qbdP B A₀ A₁ A₂)) ∧
      matG (qbdP B A₀ A₁ A₂) = matMulE (seriesInvE (matU (qbdP B A₀ A₁ A₂))) (ennMat A₂) ∧
      ∀ X Y : ι → ι → ℝ, (∀ i j, 0 ≤ X i j) → (∀ i j, 0 ≤ Y i j) →
        (∀ i j, seriesInvE (ennMat X) i j ≠ ⊤) →
        ennMat X = ennMat A₁ + matMulE (ennMat A₀) (ennMat Y) →
        ennMat Y = matMulE (seriesInvE (ennMat X)) (ennMat A₂) →
        ∀ i j, matU (qbdP B A₀ A₁ A₂) i j ≤ ennMat X i j ∧
          matG (qbdP B A₀ A₁ A₂) i j ≤ ennMat Y i j := by sorry

end MatrixAnalytic.MinimalSolutions
