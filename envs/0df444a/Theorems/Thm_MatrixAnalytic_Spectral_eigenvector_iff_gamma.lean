-- Prove2me | Theorems.Thm_MatrixAnalytic_Spectral_eigenvector_iff_gamma
-- name    : MatrixAnalytic.Spectral.eigenvector_iff_gamma
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:45:58.688989+00:00
-- url     : https://prove2.me/theorems/dba71154-0fd7-44af-b476-351ae5c86d96
-- title:
--   Theorem 9.4.1 — eigenvectors of G are the null vectors of Γ(λ)
-- statement:
--   Let $P$ be the transition matrix (6.1) of a homogeneous QBD with blocks $B, A_0, A_1, A_2$ and finitely many phases; assume $P$ stochastic and irreducible, $A = A_0 + A_1 + A_2$ irreducible, and the QBD positive recurrent. Let $G$ be its first-passage matrix and $\Gamma(x) = x^2A_0 + x(A_1 - I) + A_2$, $\gamma(x) = \det\Gamma(x)$. For a complex number $\lambda$:
--
--   1. $\lambda$ is an eigenvalue of $G$ if and only if $\gamma(\lambda) = 0$ and $|\lambda| \le 1$;
--   2. if $\lambda$ is an eigenvalue of $G$, a nonzero column vector $v$ is an eigenvector of $G$ associated with $\lambda$ if and only if
--   $$\Gamma(\lambda)v = 0.$$
--
--   Eigenvectors of $G$ can thus be computed from the blocks of the transition matrix alone.
--
--   **Formalization Note** "Eigenvalue of $G$" is "root of the characteristic polynomial of $G$". The book's "eigenvector" is a nonzero vector, so $v \ne 0$ is a hypothesis of the equivalence (for $v = 0$ both $Gv = \lambda v$ and $\Gamma(\lambda)v = 0$ hold trivially; see finding F1). The equivalence "an eigenvalue of $G$ or, equivalently, a root of $\gamma(x)$ in $|z| \le 1$" of the book's first sentence is clause 1.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 214, Theorem 9.4.1

import Mathlib
import Definitions.Def_MatrixAnalytic_Spectral_Chain
import Definitions.Def_MatrixAnalytic_Spectral_QBD
import Definitions.Def_MatrixAnalytic_Spectral_Polynomial

open scoped ENNReal
open Polynomial Matrix

namespace MatrixAnalytic.Spectral

/-- Theorem 9.4.1 (p. 214). For a positive recurrent irreducible QBD (6.1) with finitely many
phases and `A = A₀ + A₁ + A₂` irreducible, a complex number `λ` is an eigenvalue of the
first-passage matrix `G` if and only if it is a root of `γ(x) = det Γ(x)` with `|λ| ≤ 1`; and for
such `λ`, a nonzero column vector `v` is an eigenvector of `G` for `λ` if and only if
`Γ(λ)v = 0`, where `Γ(x) = x²A₀ + x(A₁ − I) + A₂`. -/
theorem eigenvector_iff_gamma {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (B A₀ A₁ A₂ : ι → ι → ℝ)
    (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂))
    (hA : IrreducibleC (matA A₀ A₁ A₂))
    (hpos : IsPositiveRecurrentChain (qbdP B A₀ A₁ A₂))
    (lam : ℂ) :
    ((matGc (qbdP B A₀ A₁ A₂)).charpoly.IsRoot lam ↔
        ((gammaPoly A₀ A₁ A₂).IsRoot lam ∧ ‖lam‖ ≤ 1)) ∧
      ((matGc (qbdP B A₀ A₁ A₂)).charpoly.IsRoot lam →
        ∀ v : ι → ℂ, v ≠ 0 →
          (matGc (qbdP B A₀ A₁ A₂) *ᵥ v = lam • v ↔ GammaAt A₀ A₁ A₂ lam *ᵥ v = 0))
      := by sorry

end MatrixAnalytic.Spectral
