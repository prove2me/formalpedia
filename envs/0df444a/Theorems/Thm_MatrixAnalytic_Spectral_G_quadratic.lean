-- Prove2me | Theorems.Thm_MatrixAnalytic_Spectral_G_quadratic
-- name    : MatrixAnalytic.Spectral.G_quadratic
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:45:57.521182+00:00
-- url     : https://prove2.me/theorems/42ca27d9-a7d0-445c-8a46-144475320645
-- title:
--   Eq. (9.1) — the first-passage matrix G solves A₀G² + (A₁ − I)G + A₂ = 0
-- statement:
--   Let $P$ be the transition matrix (6.1) of a homogeneous QBD with blocks $B, A_0, A_1, A_2$ and finitely many phases $m$, and assume $P$ is stochastic and irreducible. Let $G$ be its first-passage matrix: $G_{ij}$ is the probability, starting from $(1, i)$, of reaching the level $0$ in a finite time and doing so first in $(0, j)$. Then
--   $$A_0G^2 + (A_1 - I)G + A_2 = 0. \tag{9.1}$$
--
--   This is (6.14) of Theorem 6.2.10, the equation from which Chapter 9 builds the matrix polynomial $\Gamma(x) = x^2A_0 + x(A_1 - I) + A_2$: $G$ is a matrix root of $\Gamma$.
--
--   **Formalization Note** $G$ is the trajectory-sum definition of the definition item `QBD`, read as a complex matrix. The hypotheses are those of Chapter 6, where (6.14) is proved; the Chapter 9 restrictions (positive recurrence, $A$ irreducible) are not needed and not assumed.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 212, Eq. (9.1) (= Eq. (6.14), Theorem 6.2.10, p. 138)

import Mathlib
import Definitions.Def_MatrixAnalytic_Spectral_Chain
import Definitions.Def_MatrixAnalytic_Spectral_QBD
import Definitions.Def_MatrixAnalytic_Spectral_Polynomial

open scoped ENNReal
open Polynomial Matrix

namespace MatrixAnalytic.Spectral

/-- Eq. (9.1) (p. 212) = (6.14) of Theorem 6.2.10 (p. 138). For an irreducible QBD (6.1) with
finitely many phases, the first-passage matrix `G` (`G_{ij}` the probability, starting from
`(1, i)`, of reaching `ℓ(0)` in finite time and first in `(0, j)`) solves
`A₀G² + (A₁ − I)G + A₂ = 0`. Matrices are read in `ℂ`. -/
theorem G_quadratic {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (B A₀ A₁ A₂ : ι → ι → ℝ)
    (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂)) :
    cMat A₀ * matGc (qbdP B A₀ A₁ A₂) ^ 2 + (cMat A₁ - 1) * matGc (qbdP B A₀ A₁ A₂)
      + cMat A₂ = 0 := by sorry

end MatrixAnalytic.Spectral
