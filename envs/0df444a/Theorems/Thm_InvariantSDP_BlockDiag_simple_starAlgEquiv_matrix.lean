-- Prove2me | Theorems.Thm_InvariantSDP_BlockDiag_simple_starAlgEquiv_matrix
-- name    : InvariantSDP.BlockDiag.simple_starAlgEquiv_matrix
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:39:55.982357+00:00
-- url     : https://prove2.me/theorems/8975fb2d-51a9-4922-bcaf-e87ecea4d592
-- title:
--   p. 14 — every simple matrix ∗-algebra is ∗-isomorphic to a full matrix algebra $\mathbb C^{k\times k}$
-- statement:
--   Let $\mathcal A \subseteq \mathbb C^{n\times n}$ be a simple matrix ∗-algebra: $\mathcal A \neq \{0\}$, and its center is $\mathbb C E$ for the unit $E$ of $\mathcal A$. Then there is $k$ such that $\mathcal A$ is ∗-isomorphic to the full matrix algebra $\mathbb C^{k\times k}$:
--   $$\varphi : \mathcal A \xrightarrow{\ \cong\ } \mathbb C^{k\times k},$$
--   where $\varphi$ is a linear bijection with $\varphi(XY) = \varphi(X)\varphi(Y)$ and $\varphi(X^*) = \varphi(X)^*$ (Definition 2.6).
--
--   This is the second ingredient of Theorem 2.7; the paper proves it on pp. 14–15 by exhibiting a unitary $U$ with $U\mathcal A U^* = \{(a_{ij} I)_{i,j=1}^k : a_{ij} \in \mathbb C\}$.
--
--   **Formalization Note** A ∗-isomorphism is Mathlib's `StarAlgEquiv ℂ` (`≃⋆ₐ[ℂ]`) between the subtype of $\mathcal A$ and `Matrix (Fin k) (Fin k) ℂ`: additive, multiplicative, $\mathbb C$-linear, star-preserving and bijective. It does not require the unit of $\mathcal A$ to map to $1$, exactly as Definition 2.6 does not, although for a bijection this follows.
-- source:
--   Bachoc, Gijswijt, Schrijver & Vallentin, Invariant semidefinite programs, arXiv:1007.2905v2, p. 14 (proved pp. 14–15); Definition 2.6, p. 13

import Mathlib
import Definitions.Def_InvariantSDP_BlockDiag_Basic

namespace InvariantSDP.BlockDiag

/-- p. 14 (proved pp. 14–15): every simple matrix ∗-algebra is ∗-isomorphic to a full matrix algebra. -/
theorem simple_starAlgEquiv_matrix {n : ℕ} (A : NonUnitalStarSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ))
    (hA : IsSimple A) :
    ∃ k : ℕ, Nonempty (A ≃⋆ₐ[ℂ] Matrix (Fin k) (Fin k) ℂ) := by sorry

end InvariantSDP.BlockDiag
