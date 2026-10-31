-- Prove2me | Theorems.Thm_MinVolEllipsoid_lemma_3
-- name    : MinVolEllipsoid.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:43:46.475979+00:00
-- url     : https://prove2.me/theorems/0a9f6cbb-4101-48ff-bd87-200fa89dd06b
-- title:
--   Lemma 3: a quadratic form vanishing on a set with nonempty interior is zero
-- statement:
--   Let $M\in\mathbb S^K$ be a symmetric matrix and $S\subseteq\mathbb R^K$ a set with nonempty interior. If
--
--   $$
--   v^\top Mv=0\qquad\text{for all }v\in S,
--   $$
--
--   then $M=0$.
--
--   The paper uses it to show that the copositive cone $\mathcal C(\mathcal K)$ of a cone with nonempty interior is pointed.
--
--   **Formalization Note** $\mathbb R^K$ is `Fin n → ℝ` with its product topology, and $v^\top Mv$ is `v ⬝ᵥ (M *ᵥ v)`.
--
--   Differences from the source: none.
-- source:
--   Mittal & Hanasusanto, Finding Minimum Volume Circumscribing Ellipsoids Using Generalized Copositive Programming, arXiv:1807.07507v4, Lemma 3, p.7

import Mathlib

open Matrix

namespace MinVolEllipsoid

/-- **Lemma 3** (Mittal & Hanasusanto, arXiv:1807.07507v4, Lemma 3, p.7). Let `M ∈ 𝕊ᴷ` be a
symmetric matrix and `S ⊆ ℝᴷ` be a set with nonempty interior. If `v⊤Mv = 0` for all `v ∈ S`,
then `M = 0`.

**Formalization Note** `ℝᴷ` is `Fin n → ℝ` with its product (Euclidean) topology; `v⊤Mv` is
`v ⬝ᵥ (M *ᵥ v)`. -/
theorem lemma_3 {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) (S : Set (Fin n → ℝ))
    (hS : (interior S).Nonempty) (hv : ∀ v ∈ S, v ⬝ᵥ (M *ᵥ v) = 0) : M = 0 := by sorry

end MinVolEllipsoid
