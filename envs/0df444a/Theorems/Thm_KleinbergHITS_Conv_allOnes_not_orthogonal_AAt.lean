-- Prove2me | Theorems.Thm_KleinbergHITS_Conv_allOnes_not_orthogonal_AAt
-- name    : KleinbergHITS.Conv.allOnes_not_orthogonal_AAt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:19:20.021018+00:00
-- url     : https://prove2.me/theorems/4e4da411-70c3-452a-99c0-d68145d47069
-- title:
--   §3, proof of Theorem 3.1, p. 11 — z is not orthogonal to ω₁(AAᵀ)
-- statement:
--   Let $A$ be the adjacency matrix of a directed graph on $n$ pages and $z=(1,\dots,1)\in\mathbb R^n$. Suppose $AA^{\top}$ satisfies Assumption (†). Then for every principal eigenvector $\omega$ of $AA^{\top}$,
--   $$\langle z,\omega\rangle=\sum_{i=1}^n\omega_i\ne0.$$
--
--   Together with the power-iteration milestone and the closed form of $y_k$, this gives the convergence of the hub weights $y_k$.
--
--   **Formalization Note** "Not orthogonal to $\omega_1(AA^{\top})$" is stated for every unit vector spanning the principal eigenspace; under (†) there are exactly two, $\pm\omega_1$, so this is the same condition. Only (†) for $AA^{\top}$ is assumed; (†) for $A^{\top}A$, a standing assumption of the paper, is dropped because it is not needed, which makes the statement stronger.
-- source:
--   Kleinberg, Authoritative sources in a hyperlinked environment, J. ACM 46(5) (1999), author's copy, p. 11, §3, proof of Theorem 3.1, third paragraph ("Consequently, z is not orthogonal to ω₁(AAᵀ)")

import Mathlib
import Definitions.Def_KleinbergHITS_Conv_Setting

namespace KleinbergHITS.Conv

open Matrix

/-- Kleinberg (1999), §3, proof of Theorem 3.1, p. 11: "z is not orthogonal to ω₁(AAᵀ)", under
Assumption (†) for `AAᵀ`. -/
theorem allOnes_not_orthogonal_AAt {n : ℕ} (E : Fin n → Fin n → Prop) [DecidableRel E]
    (hAAt : Dagger (adjMatrix E * (adjMatrix E)ᵀ)) :
    ∀ ω, IsPrincipalEigenvector (adjMatrix E * (adjMatrix E)ᵀ) ω → allOnes n ⬝ᵥ ω ≠ 0 := by sorry

end KleinbergHITS.Conv
