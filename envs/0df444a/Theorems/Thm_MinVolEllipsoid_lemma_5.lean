-- Prove2me | Theorems.Thm_MinVolEllipsoid_lemma_5
-- name    : MinVolEllipsoid.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:44:41.864932+00:00
-- url     : https://prove2.me/theorems/87850eec-ad43-4e11-895a-0301ccc1ed3e
-- title:
--   Lemma 5: $M\succeq_{\mathcal C(\mathcal K)}A^\top A$ iff some $H\succeq0$ has $M\succeq_{\mathcal C(\mathcal K)}H$ and $[H\ A^\top;\ A\ \mathbb I]\succeq0$
-- statement:
--   Let $M\in\mathbb S^K$ be a symmetric matrix and $A\in\mathbb R^{J\times K}$ an arbitrary matrix. Then for every proper cone $\mathcal K\subset\mathbb R^K$,
--
--   $$
--   M\succeq_{\mathcal C(\mathcal K)}A^\top A
--   \quad\Longleftrightarrow\quad
--   \exists\,H\in\mathbb S^K_+:\quad M\succeq_{\mathcal C(\mathcal K)}H\quad\text{and}\quad\begin{bmatrix}H & A^\top\\ A & \mathbb I\end{bmatrix}\succeq0.\qquad(5)
--   $$
--
--   The lemma replaces a copositive constraint that is quadratic in $A$ by one copositive and one semidefinite constraint that are linear in $(A,H)$; the paper applies it with $\mathbb R^{K+1}$ in place of $\mathbb R^K$ and $[A\ b]$ in place of $A$ to turn (9) into (3).
--
--   **Formalization Note** $\mathbb R^K$ and $\mathbb R^J$ are `ι → ℝ` and `κ → ℝ` for arbitrary finite index types. $P\succeq_{\mathcal C(\mathcal K)}Q$ is `GenCopositive 𝒦 (P - Q)`; $H\in\mathbb S^K_+$ and $\succeq0$ are `Matrix.PosSemidef`; the block matrix is `Matrix.fromBlocks H Aᵀ A 1`. "Proper" is the published `EJASpectral.RootDet.IsProperCone`.
--
--   Differences from the source:
--
--   - encoding: M ∈ 𝕊ᴷ, A ∈ ℝ^{J×K}, 𝒦 ⊂ ℝᴷ → M : Matrix ι ι ℝ, A : Matrix κ ι ℝ, C : Set (ι → ℝ) for arbitrary finite index types ι, κ; reason: ℝᴷ is ι → ℝ with |ι| = K and ℝᴶ is κ → ℝ with |κ| = J; every K, J ≥ 0 is an instance and no instance is added
-- source:
--   Mittal & Hanasusanto, Finding Minimum Volume Circumscribing Ellipsoids Using Generalized Copositive Programming, arXiv:1807.07507v4, Lemma 5, display (5), p.7

import Mathlib
import Definitions.Def_MinVolEllipsoid_GenCopositive
import Definitions.Def_EJASpectral_RootDet_LHSCB

open Matrix

namespace MinVolEllipsoid

/-- **Lemma 5** (Mittal & Hanasusanto, arXiv:1807.07507v4, Lemma 5, display (5), p.7). Let
`M ∈ 𝕊ᴷ` be a symmetric matrix and `A ∈ ℝ^{J×K}` be an arbitrary matrix. Then, for any proper
cone `𝒦 ⊂ ℝᴷ`, the inequality `M ⪰_{𝒞(𝒦)} A⊤A` is satisfied if and only if there exists a matrix
`H ∈ 𝕊ᴷ₊` such that `M ⪰_{𝒞(𝒦)} H` and `[H A⊤; A 𝕀] ⪰ 0`.

**Formalization Note** `ℝᴷ` and `ℝᴶ` are `ι → ℝ` and `κ → ℝ` for arbitrary finite index types.
`P ⪰_{𝒞(𝒦)} Q` is `GenCopositive C (P - Q)`; `H ∈ 𝕊ᴷ₊` and `⪰ 0` are `Matrix.PosSemidef`; the
block matrix is `Matrix.fromBlocks H Aᵀ A 1`. "Proper" is the published
`EJASpectral.RootDet.IsProperCone`. -/
theorem lemma_5 {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (M : Matrix ι ι ℝ) (hM : M.IsSymm) (A : Matrix κ ι ℝ) (C : Set (ι → ℝ))
    (hC : EJASpectral.RootDet.IsProperCone C) :
    GenCopositive C (M - Aᵀ * A) ↔
      ∃ H : Matrix ι ι ℝ, H.PosSemidef ∧ GenCopositive C (M - H) ∧
        (fromBlocks H Aᵀ A (1 : Matrix κ κ ℝ)).PosSemidef := by sorry

end MinVolEllipsoid
