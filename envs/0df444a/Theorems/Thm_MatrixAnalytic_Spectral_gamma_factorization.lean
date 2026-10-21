-- Prove2me | Theorems.Thm_MatrixAnalytic_Spectral_gamma_factorization
-- name    : MatrixAnalytic.Spectral.gamma_factorization
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:45:57.951927+00:00
-- url     : https://prove2.me/theorems/dc8420ba-169a-4a8e-9b74-c5ec2a8a91f4
-- title:
--   Eq. (9.3) — Γ(x) = Φ_G(x)(xI − G)
-- statement:
--   Let $P$ be the transition matrix (6.1) of a homogeneous QBD with blocks $B, A_0, A_1, A_2$ and finitely many phases, stochastic and irreducible, and let $G$ be its first-passage matrix. Then for every complex $x$,
--   $$\Gamma(x) = \Phi_G(x)(xI - G), \tag{9.3}$$
--   where $\Gamma(x) = x^2A_0 + x(A_1 - I) + A_2$ and $\Phi_G(x) = xA_0 + A_1 - I + A_0G$.
--
--   Taking determinants, $\gamma(x) = \det\Phi_G(x)\,\det(xI - G)$, so every eigenvalue of $G$ is a root of $\gamma$ with at least the same multiplicity; this is the first step of the proof of Theorem 9.3.1.
--
--   **Formalization Note** $G$ is the trajectory-sum first-passage matrix read in $\mathbb C$, and the identity is stated pointwise for every $x \in \mathbb C$.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 212, Eq. (9.3) (proof of Theorem 9.3.1)

import Mathlib
import Definitions.Def_MatrixAnalytic_Spectral_Chain
import Definitions.Def_MatrixAnalytic_Spectral_QBD
import Definitions.Def_MatrixAnalytic_Spectral_Polynomial

open scoped ENNReal
open Polynomial Matrix

namespace MatrixAnalytic.Spectral

/-- Eq. (9.3) (p. 212). For an irreducible QBD (6.1) with finitely many phases and first-passage
matrix `G`, the matrix polynomial `Γ(x) = x²A₀ + x(A₁ − I) + A₂` factors, for every `x ∈ ℂ`, as
`Γ(x) = Φ_G(x)(xI − G)` with `Φ_G(x) = xA₀ + A₁ − I + A₀G`. -/
theorem gamma_factorization {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (B A₀ A₁ A₂ : ι → ι → ℝ)
    (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂)) :
    ∀ x : ℂ, GammaAt A₀ A₁ A₂ x =
      PhiG A₀ A₁ (matGc (qbdP B A₀ A₁ A₂)) x * (x • (1 : Matrix ι ι ℂ) - matGc (qbdP B A₀ A₁ A₂))
      := by sorry

end MatrixAnalytic.Spectral
