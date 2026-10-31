-- Prove2me | Theorems.Thm_MinVolEllipsoid_lemma_4
-- name    : MinVolEllipsoid.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:45:56.423685+00:00
-- url     : https://prove2.me/theorems/3494c7b5-7d12-43b4-b834-91ea871d1696
-- title:
--   Lemma 4: a Slater point $[X\ x;\ x^\top\ 1]\succ_{\mathcal C^*(\mathcal K)}0$ exists
-- statement:
--   Let $\mathcal P\subseteq\mathbb R^K$ satisfy Assumption 1 (p.1): $\mathcal P$ is compact, convex and full-dimensional (has nonempty interior). Let $\mathcal K=\mathrm{cone}(\{[x;1]:x\in\mathcal P\})\subseteq\mathbb R^{K+1}$ be the cone of display (2). Then there exist $X\in\mathbb S^K$ and $x\in\mathbb R^K$ such that
--
--   $$
--   \begin{bmatrix}X & x\\ x^\top & 1\end{bmatrix}\succ_{\mathcal C^*(\mathcal K)}0,
--   $$
--
--   that is, the matrix lies in the interior of the generalized completely positive cone $\mathcal C^*(\mathcal K)$.
--
--   This is a strictly feasible (Slater) point of the completely positive program (7), which gives strong duality between (7) and its dual (8) together with attainment in the dual.
--
--   **Formalization Note** The interior of $\mathcal C^*(\mathcal K)$ is taken relative to the symmetric matrices $\mathbb S^{K+1}$ (definition `IsGenCPInterior`).
--
--   Differences from the source:
--
--   - reading: [X x; x⊤ 1] ≻_{𝒞*(𝒦)} 0, i.e. an interior point of 𝒞*(𝒦) (proof of Lemma 4, "M ∈ int(𝒞*(𝒦))") → interior relative to the symmetric matrices 𝕊^{K+1} (IsGenCPInterior); reason: 𝒞*(𝒦) ⊆ 𝕊^{K+1} by its definition on p.5; its interior in the space of all matrices is empty, so the paper's int can only mean the interior within 𝕊^{K+1}
--   - encoding: 𝒞*(𝒦): sums of I ≥ 1 terms xᵢxᵢ⊤ → sums of m ≥ 0 terms; reason: 0 ∈ 𝒦, so a zero summand can always be added; same set
--   - encoding: vectors [x; τ] ∈ ℝ^{K+1} with τ the last coordinate → Sum.elim x (fun _ => τ) : Fin n ⊕ Unit → ℝ, τ at the Unit coordinate; reason: Lean convention for ℝ^{K+1}; same vectors
--   - encoding: 𝒫 full-dimensional (Assumption 1) → (interior P).Nonempty; reason: the paper's own reading in the proof of Lemma 2, p.7 ("Since 𝒫 has nonempty interior")
--   - encoding: 𝒦 = cone({[x; 1] : x ∈ 𝒫}), the conic hull → liftCone P, the finite nonnegative combinations of the lifted points (including 0); reason: the conic hull of a set is the set of its finite nonnegative combinations
-- source:
--   Mittal & Hanasusanto, Finding Minimum Volume Circumscribing Ellipsoids Using Generalized Copositive Programming, arXiv:1807.07507v4, Lemma 4, p.7

import Mathlib
import Definitions.Def_MinVolEllipsoid_liftCone
import Definitions.Def_MinVolEllipsoid_IsGenCPInterior
import Definitions.Def_MinVolEllipsoid_borderedMatrix

namespace MinVolEllipsoid

/-- **Lemma 4** (Mittal & Hanasusanto, arXiv:1807.07507v4, Lemma 4, p.7). Let `𝒦` be the cone
defined in (2). There exist `X ∈ 𝕊ᴷ` and `x ∈ ℝᴷ` such that `[X x; x⊤ 1] ≻_{𝒞*(𝒦)} 0`, i.e. the
matrix lies in the interior of `𝒞*(𝒦)`.

Here `𝒦 = liftCone P` for a set `P ⊆ ℝᴷ` satisfying Assumption 1 (p.1).

**Formalization Note** The interior of `𝒞*(𝒦)` is taken relative to the symmetric matrices
`𝕊ᴷ⁺¹` (`MinVolEllipsoid.IsGenCPInterior`). `[X x; x⊤ 1]` is `borderedMatrix X x x 1` over
`Fin n ⊕ Unit`. -/
theorem lemma_4 {n : ℕ} (P : Set (Fin n → ℝ)) (hPc : IsCompact P) (hPcv : Convex ℝ P)
    (hPi : (interior P).Nonempty) :
    ∃ (X : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ),
      X.IsSymm ∧ IsGenCPInterior (liftCone P) (borderedMatrix X x x 1) := by sorry

end MinVolEllipsoid
