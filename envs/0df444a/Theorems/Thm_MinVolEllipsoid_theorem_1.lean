-- Prove2me | Theorems.Thm_MinVolEllipsoid_theorem_1
-- name    : MinVolEllipsoid.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:45:47.109+00:00
-- url     : https://prove2.me/theorems/f18f610e-6ae9-421c-ae64-1282369f6626
-- title:
--   Theorem 1: $\mathcal E(A,b)\supseteq\mathcal P$ iff a copositive and a semidefinite condition (3) hold
-- statement:
--   Let $\mathcal P\subseteq\mathbb R^K$ satisfy Assumption 1: $\mathcal P$ is compact, convex and full-dimensional. Let the cone $\mathcal K\subseteq\mathbb R^{K+1}$ be
--
--   $$
--   \mathcal K=\mathrm{cone}\bigl(\{[x;1]:x\in\mathcal P\}\bigr).\qquad(2)
--   $$
--
--   If $A\in\mathbb S^K_{++}$ and $b\in\mathbb R^K$, then the ellipsoid $\mathcal E(A,b)=\{x:\|Ax+b\|^2\le1\}$ contains $\mathcal P$ if and only if there exist $F\in\mathbb S^K$, $g\in\mathbb R^K$, $h\in\mathbb R$ such that
--
--   $$
--   \begin{bmatrix}F & g\\ g^\top & h-1\end{bmatrix}\preceq_{\mathcal C(\mathcal K)}0
--   \qquad\text{and}\qquad
--   \begin{bmatrix}F & g & A\\ g^\top & h & b^\top\\ A & b & \mathbb I\end{bmatrix}\succeq0.\qquad(3)
--   $$
--
--   Here $\mathcal C(\mathcal K)=\{M\in\mathbb S^{K+1}:v^\top Mv\ge0\ \forall v\in\mathcal K\}$ is the cone of generalized copositive matrices. Replacing the constraint $Z(A,b)\le1$ of the minimum volume ellipsoid problem (MVE) by (3) gives an exact generalized copositive program (4) for the minimum volume ellipsoid circumscribing $\mathcal P$; its tractable inner approximations give the paper's SDP approximations.
--
--   **Formalization Note** $\mathcal E(A,b)$ is the published `ConvexOptimization.ellipsoidBody A b`. $A\in\mathbb S^K_{++}$ is `Matrix.PosDef A`, $F\in\mathbb S^K$ is `F.IsSymm`. $M\preceq_{\mathcal C(\mathcal K)}0$ is `GenCopositive 𝒦 (-M)`, and $\succeq0$ is `Matrix.PosSemidef`.
--
--   Differences from the source:
--
--   - encoding: ‖Ax + b‖² with the Euclidean norm → (A *ᵥ x + b) ⬝ᵥ (A *ᵥ x + b) via ConvexOptimization.ellipsoidBody; reason: the pi type carries the sup norm; the dot product is the squared Euclidean norm
--   - encoding: vectors [x; τ] ∈ ℝ^{K+1} with τ the last coordinate → Sum.elim x (fun _ => τ) : Fin n ⊕ Unit → ℝ, τ at the Unit coordinate; reason: Lean convention for ℝ^{K+1}; same vectors
--   - encoding: 𝒫 full-dimensional (Assumption 1) → (interior P).Nonempty; reason: the paper's own reading in the proof of Lemma 2, p.7 ("Since 𝒫 has nonempty interior")
--   - encoding: 𝒦 = cone({[x; 1] : x ∈ 𝒫}), the conic hull → liftCone P, the finite nonnegative combinations of the lifted points (including 0); reason: the conic hull of a set is the set of its finite nonnegative combinations
-- source:
--   Mittal & Hanasusanto, Finding Minimum Volume Circumscribing Ellipsoids Using Generalized Copositive Programming, arXiv:1807.07507v4, Theorem 1, displays (2)–(3), p.6

import Mathlib
import Definitions.Def_MinVolEllipsoid_liftCone
import Definitions.Def_MinVolEllipsoid_GenCopositive
import Definitions.Def_MinVolEllipsoid_borderedMatrix
import Definitions.Def_MinVolEllipsoid_ineq3Right
import Definitions.Def_ConvexOptimization_ellipsoidBody

namespace MinVolEllipsoid

/-- **Theorem 1** (Mittal & Hanasusanto, *Finding Minimum Volume Circumscribing Ellipsoids Using
Generalized Copositive Programming*, arXiv:1807.07507v4, Theorem 1, displays (2)–(3), p.6).

Let `𝒫` be a set satisfying Assumption 1 (p.1: compact, convex, and full-dimensional). Let the cone
`𝒦 ⊆ ℝᴷ⁺¹` be defined as `𝒦 = cone({[x; 1] : x ∈ 𝒫})` (2). If `A ∈ 𝕊ᴷ₊₊` and `b ∈ ℝᴷ`, then the
ellipsoid `ℰ(A, b)` contains `𝒫` if and only if there exist `F ∈ 𝕊ᴷ`, `g ∈ ℝᴷ`, `h ∈ ℝ` such that

`[F g; g⊤ h − 1] ⪯_{𝒞(𝒦)} 0` and `[F g A; g⊤ h b⊤; A b 𝕀] ⪰ 0`. (3)

**Formalization Note** The dimension is `n` (the paper's `K`). "Full-dimensional" is
`(interior P).Nonempty`. `𝒦` is `liftCone P` over `Fin n ⊕ Unit`, the `Unit` coordinate being the
paper's last coordinate. `ℰ(A, b)` is the published `ConvexOptimization.ellipsoidBody A b`
(`‖Ax + b‖²` as a dot product). `A ∈ 𝕊ᴷ₊₊` is `Matrix.PosDef A`; `F ∈ 𝕊ᴷ` is `F.IsSymm`.
`M ⪯_{𝒞(𝒦)} 0` is `GenCopositive 𝒦 (-M)`; `⪰ 0` is `Matrix.PosSemidef`. The second matrix of (3) is
`MinVolEllipsoid.ineq3Right A b F g h`, copied literally from the page. -/
theorem theorem_1 {n : ℕ} (P : Set (Fin n → ℝ)) (hPc : IsCompact P) (hPcv : Convex ℝ P)
    (hPi : (interior P).Nonempty) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (b : Fin n → ℝ) :
    P ⊆ ConvexOptimization.ellipsoidBody A b ↔
      ∃ (F : Matrix (Fin n) (Fin n) ℝ) (g : Fin n → ℝ) (h : ℝ), F.IsSymm ∧
        GenCopositive (liftCone P) (-(borderedMatrix F g g (h - 1))) ∧
        (ineq3Right A b F g h).PosSemidef := by sorry

end MinVolEllipsoid
