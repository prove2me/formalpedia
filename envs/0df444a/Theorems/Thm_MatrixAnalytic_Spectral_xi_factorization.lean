-- Prove2me | Theorems.Thm_MatrixAnalytic_Spectral_xi_factorization
-- name    : MatrixAnalytic.Spectral.xi_factorization
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:46:07.490557+00:00
-- url     : https://prove2.me/theorems/8834bd06-663a-473a-b750-085a7a12bcd8
-- title:
--   Proof of Theorem 9.3.1 — Ξ(x) = (xI − R)Φ_R(x)
-- statement:
--   Let $P$ be the transition matrix (6.1) of a homogeneous QBD with blocks $B, A_0, A_1, A_2$ and finitely many phases, stochastic, irreducible and positive recurrent, and let $R$ be its rate matrix: $R_{ij}$ is the expected number of visits to $(1, j)$, starting from $(0, i)$, before the first return to the level $0$. Then the entries of $R$ are finite, and for every complex $x$,
--   $$\Xi(x) = (xI - R)\Phi_R(x),$$
--   where $\Xi(x) = x^2A_2 + x(A_1 - I) + A_0$ and $\Phi_R(x) = xA_2 + A_1 - I + RA_2$.
--
--   This is the factorization for $R$ used in the second part of the proof of Theorem 9.3.1, mirroring (9.3) for $G$; since $\Xi(x) = x^2\Gamma(x^{-1})$, it relates the eigenvalues of $R$ to the roots of $\gamma$ outside the unit disk.
--
--   **Formalization Note** $R$ is the trajectory-sum rate matrix, computed in $[0,\infty]$ and read in $\mathbb C$; its finiteness is part of the conclusion. Positive recurrence is the return-time notion of the definition item `Chain`, the standing assumption of Chapter 9 and of Theorem 9.3.1.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, pp. 212–213, proof of Theorem 9.3.1

import Mathlib
import Definitions.Def_MatrixAnalytic_Spectral_Chain
import Definitions.Def_MatrixAnalytic_Spectral_QBD
import Definitions.Def_MatrixAnalytic_Spectral_Polynomial

open scoped ENNReal
open Polynomial Matrix

namespace MatrixAnalytic.Spectral

/-- The factorization of `Ξ` in the proof of Theorem 9.3.1 (pp. 212–213). For a positive
recurrent irreducible QBD (6.1) with finitely many phases, the entries of the rate matrix `R`
(`R_{ij}` the expected number of visits to `(1, j)` from `(0, i)` before the first return to
`ℓ(0)`) are finite, and for every `x ∈ ℂ` the matrix `Ξ(x) = x²A₂ + x(A₁ − I) + A₀` factors as
`Ξ(x) = (xI − R)Φ_R(x)` with `Φ_R(x) = xA₂ + A₁ − I + RA₂`. -/
theorem xi_factorization {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (B A₀ A₁ A₂ : ι → ι → ℝ)
    (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂))
    (hpos : IsPositiveRecurrentChain (qbdP B A₀ A₁ A₂)) :
    (∀ i j : ι, matR (qbdP B A₀ A₁ A₂) i j ≠ ⊤) ∧
      ∀ x : ℂ, XiAt A₀ A₁ A₂ x =
        (x • (1 : Matrix ι ι ℂ) - matRc (qbdP B A₀ A₁ A₂)) * PhiR A₁ A₂ (matRc (qbdP B A₀ A₁ A₂)) x
      := by sorry

end MatrixAnalytic.Spectral
