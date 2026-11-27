-- Prove2me | Theorems.Thm_MinVolEllipsoid_Supplement_lemma_6
-- name    : MinVolEllipsoid.Supplement.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T22:33:55.550298+00:00
-- url     : https://prove2.me/theorems/3c6b3688-0b90-5449-99d2-274546b7041b
-- title:
--   Lemma 6 — $\det\bigl(\tfrac12(M+M^\top)\bigr)\le\det M$ when $M+M^\top\succ0$
-- statement:
--   Let $M\in\mathbb R^{K\times K}$ be a real square matrix, not necessarily symmetric, such that $M+M^\top$ is positive definite. Then
--
--   $$
--   \det\Bigl(\tfrac12\bigl(M+M^\top\bigr)\Bigr)\le\det(M).
--   $$
--
--   The paper cites this as [25, Theorem 7.8.7] (Horn and Johnson, *Matrix Analysis*) and uses it in the proof of Theorem 3 to compare the dual objective (14), which involves the determinant of a symmetric part, with the determinant of the constructed matrix $A$.
--
--   **Formalization Note** The dimension is $n$. The conclusion concerns $\det M$ itself, not its absolute value.
--
--   Differences from the source: none.
-- source:
--   Mittal & Hanasusanto, Finding Minimum Volume Circumscribing Ellipsoids Using Generalized Copositive Programming, arXiv:1807.07507v4, Lemma 6, p.11 (citing Horn & Johnson, Matrix Analysis, Theorem 7.8.7)

import Mathlib

open Matrix

namespace MinVolEllipsoid.Supplement

/-- **Lemma 6** (Mittal & Hanasusanto, arXiv:1807.07507v4, Lemma 6, p.11, citing Horn–Johnson,
*Matrix Analysis*, Theorem 7.8.7).

If `M ∈ ℝ^{K×K}` is a square matrix with real entries such that `M + M⊤ ≻ 0`, then

`det(½(M + M⊤)) ≤ det(M)`.

**Formalization Note** The dimension is `n` (the paper's `K`). `M + M⊤ ≻ 0` is
`(M + Mᵀ).PosDef`. The conclusion is about `det M` itself, without absolute value. -/
theorem lemma_6 {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : (M + Mᵀ).PosDef) :
    ((1 / 2 : ℝ) • (M + Mᵀ)).det ≤ M.det := by sorry

end MinVolEllipsoid.Supplement
