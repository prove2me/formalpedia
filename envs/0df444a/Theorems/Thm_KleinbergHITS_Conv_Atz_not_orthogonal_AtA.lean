-- Prove2me | Theorems.Thm_KleinbergHITS_Conv_Atz_not_orthogonal_AtA
-- name    : KleinbergHITS.Conv.Atz_not_orthogonal_AtA
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:19:22.816577+00:00
-- url     : https://prove2.me/theorems/a1576d61-0375-4f03-bcd3-0fda608e5675
-- title:
--   §3, proof of Theorem 3.1, p. 11 — if λ₁(AᵀA) ≠ 0 then Aᵀz is not orthogonal to ω₁(AᵀA)
-- statement:
--   Let $A$ be the adjacency matrix of a directed graph on $n$ pages and $z=(1,\dots,1)\in\mathbb R^n$. Suppose $\lambda_1$ is the principal eigenvalue of $A^{\top}A$ in the sense of Assumption (†) — its eigenspace is a line and every other eigenvalue is strictly smaller in absolute value — and that
--   $$\lambda_1(A^{\top}A)\ne0.$$
--   Then for every principal eigenvector $\omega$ of $A^{\top}A$,
--   $$\langle A^{\top}z,\omega\rangle\ne0.$$
--
--   Together with the power-iteration milestone and the closed form of $x_k$, this gives the convergence of the authority weights $x_k$.
--
--   **Formalization Note** The page's hypothesis "$\lambda_1(A^{\top}A)\ne0$ (as dictated by Assumption (†))" is written out as the two hypotheses `IsPrincipalEigenvalue (AᵀA) λ₁` and `λ₁ ≠ 0` (together they are exactly (†) for $A^{\top}A$ in the mission's encoding). (†) for $AA^{\top}$ is not assumed, which makes the statement stronger. "Not orthogonal" is stated for every principal eigenvector, which under (†) means both $\pm\omega_1$.
-- source:
--   Kleinberg, Authoritative sources in a hyperlinked environment, J. ACM 46(5) (1999), author's copy, p. 11, §3, proof of Theorem 3.1, third paragraph ("Similarly, one can show that if λ₁(AᵀA) ≠ 0 (as dictated by Assumption (†)), then Aᵀz is not orthogonal to ω₁(AᵀA)")

import Mathlib
import Definitions.Def_KleinbergHITS_Conv_Setting

namespace KleinbergHITS.Conv

open Matrix

/-- Kleinberg (1999), §3, proof of Theorem 3.1, p. 11: "if λ₁(AᵀA) ≠ 0 (as dictated by Assumption
(†)), then Aᵀz is not orthogonal to ω₁(AᵀA)". -/
theorem Atz_not_orthogonal_AtA {n : ℕ} (E : Fin n → Fin n → Prop) [DecidableRel E] (l₁ : ℝ)
    (hl : IsPrincipalEigenvalue ((adjMatrix E)ᵀ * adjMatrix E) l₁) (hne : l₁ ≠ 0) :
    ∀ ω, IsPrincipalEigenvector ((adjMatrix E)ᵀ * adjMatrix E) ω →
      ((adjMatrix E)ᵀ *ᵥ allOnes n) ⬝ᵥ ω ≠ 0 := by sorry

end KleinbergHITS.Conv
