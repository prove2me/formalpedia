-- Prove2me | Theorems.Thm_MinVolEllipsoid_containment_iff_Z_le_one
-- name    : MinVolEllipsoid.containment_iff_Z_le_one
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:44:39.025261+00:00
-- url     : https://prove2.me/theorems/c9e28257-dfb4-4005-a2ec-cc50a282a1c7
-- title:
--   Display (1) and p.6: $\mathcal E(A,b)\supseteq\mathcal P$ iff $Z(A,b)\le1$
-- statement:
--   Let $\mathcal P\subseteq\mathbb R^K$ satisfy Assumption 1 (p.1): $\mathcal P$ is compact, convex and full-dimensional (has nonempty interior). Let $\mathcal K=\mathrm{cone}(\{[x;1]:x\in\mathcal P\})\subseteq\mathbb R^{K+1}$ be the cone of display (2). Let $A\in\mathbb S^K_{++}$ be symmetric positive definite and $b\in\mathbb R^K$. With $Z(A,b)=\sup_{x\in\mathcal P}\|Ax+b\|^2$ as in display (1),
--
--   $$
--   \mathcal P\subseteq\mathcal E(A,b)=\{x\in\mathbb R^K:\|Ax+b\|^2\le1\}
--   \quad\Longleftrightarrow\quad Z(A,b)\le1.
--   $$
--
--   This is the statement that "the constraint $Z(A,b)\le1$ forces every element of $\mathcal P$ to lie inside the ellipsoid", which turns the minimum volume ellipsoid problem into the semi-infinite program (MVE).
--
--   **Formalization Note** $\mathcal E(A,b)$ is the published `ConvexOptimization.ellipsoidBody A b`; $A\in\mathbb S^K_{++}$ is `Matrix.PosDef A`, which includes symmetry.
--
--   Differences from the source:
--
--   - encoding: ‖Ax + b‖² with the Euclidean norm → (A *ᵥ x + b) ⬝ᵥ (A *ᵥ x + b) in ConvexOptimization.ellipsoidBody and MinVolEllipsoid.Zval; reason: the pi type carries the sup norm; the dot product is the squared Euclidean norm
--   - encoding: 𝒫 full-dimensional (Assumption 1) → (interior P).Nonempty; reason: the paper's own reading in the proof of Lemma 2, p.7 ("Since 𝒫 has nonempty interior")
-- source:
--   Mittal & Hanasusanto, Finding Minimum Volume Circumscribing Ellipsoids Using Generalized Copositive Programming, arXiv:1807.07507v4, display (1), p.5, and p.6, "The constraint Z(A, b) ≤ 1 forces every element of P to lie inside the ellipsoid"

import Mathlib
import Definitions.Def_MinVolEllipsoid_Zval
import Definitions.Def_ConvexOptimization_ellipsoidBody

namespace MinVolEllipsoid

/-- **`ℰ(A, b) ⊇ 𝒫` iff `Z(A, b) ≤ 1`** (Mittal & Hanasusanto, arXiv:1807.07507v4, display (1),
p.5, and p.6: "The constraint Z(A, b) ≤ 1 forces every element of 𝒫 to lie inside the
ellipsoid").

For `P ⊆ ℝᴷ` satisfying Assumption 1 (p.1), `A ∈ 𝕊ᴷ₊₊` and `b ∈ ℝᴷ`, the ellipsoid
`ℰ(A, b) = {x : ‖Ax + b‖² ≤ 1}` contains `P` if and only if `Z(A, b) = sup_{x∈P} ‖Ax + b‖² ≤ 1`.

**Formalization Note** `ℰ(A, b)` is the published `ConvexOptimization.ellipsoidBody A b`;
`A ∈ 𝕊ᴷ₊₊` is `Matrix.PosDef A`, which includes symmetry. -/
theorem containment_iff_Z_le_one {n : ℕ} (P : Set (Fin n → ℝ)) (hPc : IsCompact P)
    (hPcv : Convex ℝ P) (hPi : (interior P).Nonempty) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (b : Fin n → ℝ) :
    P ⊆ ConvexOptimization.ellipsoidBody A b ↔ Zval P A b ≤ 1 := by sorry

end MinVolEllipsoid
