-- Prove2me | Theorems.Thm_MatrixAnalytic_MinimalSolutions_sp_Ghat_eq_sp_R
-- name    : MatrixAnalytic.MinimalSolutions.sp_Ghat_eq_sp_R
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:44:45.890486+00:00
-- url     : https://prove2.me/theorems/5a40de7b-15c0-45d2-8571-099e8b85726d
-- title:
--   Theorem 8.2.3 — Ĝ and R have the same maximal eigenvalue
-- statement:
--   Let $X$ be an irreducible homogeneous QBD with transition matrix (8.1), with a finite number $m$ of phases, and assume that $A = A_0 + A_1 + A_2$ is irreducible. Let $R$ be the matrix of expected numbers of visits of Theorem 6.2.1 and $\hat G$ the matrix of first passage probabilities from $\ell(1)$ to $\ell(0)$ of the level-reversed QBD (8.25). Then $R$ and $\hat G$ have finite entries and the same maximal eigenvalue:
--
--   $$\mathrm{sp}(\hat G) = \mathrm{sp}(R).$$
--
--   Thus the convergence rate $\xi = \mathrm{sp}(\hat G)$ of the linear progression algorithm equals the caudal characteristic $\eta = \mathrm{sp}(R)$ of the QBD.
--
--   **Formalization Note** For these nonnegative matrices the maximal eigenvalue is the Perron–Frobenius eigenvalue, which equals the spectral radius; the statement compares spectral radii of the two matrices viewed as complex matrices. The boundary block of the level-reversed QBD is arbitrary, since $\hat G$ does not depend on it.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 178, Theorem 8.2.3

import Mathlib
import Definitions.Def_MatrixAnalytic_MinimalSolutions_Chain
import Definitions.Def_MatrixAnalytic_MinimalSolutions_QBD
import Definitions.Def_MatrixAnalytic_MinimalSolutions_Passage

open scoped ENNReal

namespace MatrixAnalytic.MinimalSolutions

/-- Theorem 8.2.3 (p. 178). For an irreducible QBD (8.1) with finitely many phases and
`A = A₀ + A₁ + A₂` irreducible, the maximal eigenvalue (spectral radius, the Perron–Frobenius
eigenvalue of these nonnegative matrices) of `Ĝ`, the first-passage matrix from `ℓ(1)` to `ℓ(0)`
of the level-reversed QBD (8.25) (any boundary block `B̂₁ = Bhat`), equals that of `R`. Both matrices
have finite entries; spectral radii are taken over `ℂ`. -/
theorem sp_Ghat_eq_sp_R {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B A₀ A₁ A₂ : ι → ι → ℝ)
    (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂))
    (hA : IrreducibleC (A₀ + A₁ + A₂))
    (Bhat : ι → ι → ℝ) :
    (∀ i j, matG (qbdP Bhat A₂ A₁ A₀) i j ≠ ⊤) ∧ (∀ i j, matR (qbdP B A₀ A₁ A₂) i j ≠ ⊤) ∧
      spectralRadius ℂ
          (Matrix.of fun i j => (((matG (qbdP Bhat A₂ A₁ A₀) i j).toReal : ℝ) : ℂ)) =
        spectralRadius ℂ
          (Matrix.of fun i j => (((matR (qbdP B A₀ A₁ A₂) i j).toReal : ℝ) : ℂ)) := by sorry

end MatrixAnalytic.MinimalSolutions
