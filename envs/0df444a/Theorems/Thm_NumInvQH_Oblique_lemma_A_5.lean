-- Prove2me | Theorems.Thm_NumInvQH_Oblique_lemma_A_5
-- name    : NumInvQH.Oblique.lemma_A_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:23:49.887975+00:00
-- url     : https://prove2.me/theorems/293d37e8-f7e0-425c-99d7-6e4cadb05c11
-- title:
--   Lemma A.5 — $L=(L\cap M)\oplus^\perp(L\cap(L\cap M)^\perp)=(L\cap M)\oplus^\perp P_LM^\perp$ (real case)
-- statement:
--   Let $n\in\mathbb N$ and let $L,M$ be linear subspaces of the Euclidean space $\mathbb R^n$. Write $\mathcal X^\perp$ for the orthogonal complement and $P_L$ for the orthogonal projector onto $L$. Then
--
--   $$L=(L\cap M)\oplus^\perp\bigl(L\cap(L\cap M)^\perp\bigr)=(L\cap M)\oplus^\perp P_LM^\perp,$$
--
--   where $\oplus^\perp$ is the orthogonal direct sum. The lemma describes the orthogonal complement of $L\cap M$ inside $L$ as the projection of $M^\perp$ onto $L$; it is used with $L=N(C)$, $M=N(A)$ in the proof of Theorem A.4(4).
--
--   **Formalization Note** The paper states the lemma in $\mathbb C^n$; this is its real specialisation, on `EuclideanSpace ℝ (Fin n)`. Each orthogonal direct sum is stated as two facts: the sum of the two subspaces is $L$, and they are orthogonal. $P_L$ is Mathlib's `Submodule.starProjection`.
-- source:
--   Černý, Czichowsky & Kallsen, Numeraire-invariant quadratic hedging and mean–variance portfolio allocation, arXiv:2110.09416v4, p. 28, Lemma A.5

import Mathlib

namespace NumInvQH.Oblique

/-- Lemma A.5, specialised from `ℂⁿ` to `ℝⁿ` (Euclidean space): for subspaces `L, M`,
`L = (L ∩ M) ⊕⊥ (L ∩ (L ∩ M)⊥) = (L ∩ M) ⊕⊥ P_L M⊥`, where `P_L` is the orthogonal projector
onto `L`. Each orthogonal direct sum is stated as "the sum equals `L` and the two summands are
orthogonal". -/
theorem lemma_A_5 {n : ℕ} (L M : Submodule ℝ (EuclideanSpace ℝ (Fin n))) :
    let PL : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) := L.starProjection
    (L ⊓ M) ⊔ (L ⊓ (L ⊓ M)ᗮ) = L ∧ (L ⊓ M) ⟂ (L ⊓ (L ⊓ M)ᗮ) ∧
    (L ⊓ M) ⊔ Mᗮ.map PL = L ∧ (L ⊓ M) ⟂ Mᗮ.map PL := by sorry

end NumInvQH.Oblique
