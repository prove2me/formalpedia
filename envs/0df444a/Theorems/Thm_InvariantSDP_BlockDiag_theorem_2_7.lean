-- Prove2me | Theorems.Thm_InvariantSDP_BlockDiag_theorem_2_7
-- name    : InvariantSDP.BlockDiag.theorem_2_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:40:01.112701+00:00
-- url     : https://prove2.me/theorems/5db38b65-7542-48ae-aae4-6165b5c2b8ea
-- title:
--   Theorem 2.7 (= Theorem 1.2), p. 13 — every matrix ∗-algebra $\mathcal A\subseteq\mathbb C^{n\times n}$ is ∗-isomorphic to $\bigoplus_{k=1}^d\mathbb C^{m_k\times m_k}$
-- statement:
--   Let $\mathcal A \subseteq \mathbb C^{n\times n}$ be a matrix ∗-algebra, i.e. a complex linear subspace closed under matrix multiplication and conjugate transpose (not necessarily containing the identity). Then there are numbers $d$ and $m_1, \dots, m_d$ and a ∗-isomorphism
--   $$\varphi : \mathcal A \longrightarrow \bigoplus_{k=1}^d \mathbb C^{m_k \times m_k}$$
--   between $\mathcal A$ and a direct sum of complete matrix algebras. Here a ∗-isomorphism is a linear bijection $\varphi$ with $\varphi(XY) = \varphi(X)\varphi(Y)$ and $\varphi(X^*) = \varphi(X)^*$ (Definition 2.6), and $\bigoplus_k \mathbb C^{m_k\times m_k}$ is the algebra of block-diagonal matrices with blocks of sizes $m_1, \dots, m_d$.
--
--   This is the structure theorem that drives symmetry reduction in semidefinite programming: an SDP whose matrix variable is restricted to $\mathcal A$ can be rewritten as an SDP over $d$ blocks of sizes $m_k$, because a ∗-isomorphism preserves positive semidefiniteness.
--
--   **Formalization Note** $\mathcal A$ is a `NonUnitalStarSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ)` (no unit assumed; $\mathcal A = \{0\}$ is allowed and needs $d = 0$). The direct sum is the product type `(k : Fin d) → Matrix (Fin (m k)) (Fin (m k)) ℂ` with pointwise operations and star, which is ∗-isomorphic to the block-diagonal algebra (Mathlib's `Matrix.blockDiagonal'`). The ∗-isomorphism is a `StarAlgEquiv ℂ`. No positivity of the $m_k$ is required, as on the page.
-- source:
--   Bachoc, Gijswijt, Schrijver & Vallentin, Invariant semidefinite programs, arXiv:1007.2905v2, p. 13, Theorem 2.7 (= Theorem 1.2, p. 6); Definition 2.6, p. 13; direct sum, p. 10

import Mathlib
import Definitions.Def_InvariantSDP_BlockDiag_Basic

namespace InvariantSDP.BlockDiag

/-- Theorem 2.7 (= Theorem 1.2), p. 13: every matrix ∗-algebra is ∗-isomorphic to a direct sum of full
matrix algebras. -/
theorem theorem_2_7 {n : ℕ} (A : NonUnitalStarSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ)) :
    ∃ (d : ℕ) (m : Fin d → ℕ),
      Nonempty (A ≃⋆ₐ[ℂ] ((k : Fin d) → Matrix (Fin (m k)) (Fin (m k)) ℂ)) := by sorry

end InvariantSDP.BlockDiag
