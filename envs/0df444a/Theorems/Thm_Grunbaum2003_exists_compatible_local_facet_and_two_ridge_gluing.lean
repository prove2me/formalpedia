-- Prove2me | Theorems.Thm_Grunbaum2003_exists_compatible_local_facet_and_two_ridge_gluing
-- name    : Grunbaum2003.exists_compatible_local_facet_and_two_ridge_gluing
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-08T21:13:29.193101+00:00
-- url     : https://prove2.me/theorems/8883e315-6f2d-4f77-9807-7843cc4989f9
-- title:
--   Compatible local facets from vertex-figure induction and two-ridge gluing for $(d+1)$-polytopes
-- statement:
--   Let $d\ge 3$ and assume Theorem 12.3.1 holds in dimension $d$. Let $P,Q\subseteq\mathbb R^{d+1}$ be $(d+1)$-polytopes, let $\varphi:\operatorname{skel}_{d-1}(P)\xrightarrow{\sim}\operatorname{skel}_{d-1}(Q)$ be an isomorphism of their $(d-1)$-skeleta, and let $F$ be a facet of $P$. Then:
--
--   1. (**Compatible local facets from vertex figures**) For every exposed vertex $v\in F$, there exists a facet $G_v$ of $Q$ (a nonempty exposed face of dimension $d$) whose upper interval at $v$ in the $(d-1)$-skeleton matches that of $F$ under $\varphi$:
--
--   $$
--   \forall S\in\operatorname{skel}_{d-1}(P),\quad v\in S\implies\bigl(\varphi(S)\subseteq G_v\iff S\subseteq F\bigr).
--   $$
--
--   2. (**Two-ridge gluing of compatible local facets**) If $G_u,G_w$ are compatible local facets of $Q$ at vertices $u,w\in F$, and $R_1\ne R_2$ are two distinct faces of $F$ in $\operatorname{skel}_{d-1}(P)$ both containing $u$ and $w$ whose images $\varphi(R_1),\varphi(R_2)$ are ridges of $Q$ (dimension $d-1$), then
--
--   $$
--   G_u=G_w.
--   $$
--
--   Together these two properties establish the local existence and pairwise ridge-gluing ingredients in the inductive proof of Theorem 12.3.1.
--
--   **Formalization Note** Polytopes in $\mathbb R^{d+1}$ are represented as subsets of `Fin (d + 1) → ℝ` satisfying `IsDPolytope`. A facet of a $(d+1)$-polytope is a nonempty exposed face whose affine span has direction of `Module.finrank` equal to $d$, and a ridge has `Module.finrank` equal to $d-1$. The $(d-1)$-skeleton is `SkeletonFace P (d + 1 - 2)`.
-- source:
--   Branko Grünbaum, Convex Polytopes, 2nd ed. (Springer GTM 221, 2003), §12.3, Theorem 12.3.1, printed p. 228 / PDF p. 270 (face-lattice formulation p. 231 / PDF p. 273)

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_SkeletonFace
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

set_option autoImplicit false

namespace Grunbaum2003

theorem exists_compatible_local_facet_and_two_ridge_gluing (d : ℕ) (hd : 3 ≤ d)
    (ih : ∀ (P Q : Set (Fin d → ℝ)), IsDPolytope P → IsDPolytope Q →
      ∀ φ : SkeletonFace P (d - 2) ≃o SkeletonFace Q (d - 2),
        ∃ Φ : PolytopeFace P ≃o PolytopeFace Q,
          ∀ F : SkeletonFace P (d - 2), Φ F.val = (φ F).val)
    (P Q : Set (Fin (d + 1) → ℝ)) (hP : IsDPolytope P) (hQ : IsDPolytope Q)
    (φ : SkeletonFace P (d + 1 - 2) ≃o SkeletonFace Q (d + 1 - 2))
    (F : PolytopeFace P)
    (hF : F.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ F.val).direction = d) :
    (∀ (v : Fin (d + 1) → ℝ), IsExposed ℝ P {v} → v ∈ F.val →
      ∃ G : PolytopeFace Q,
        G.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ G.val).direction = d ∧
        (∀ S : SkeletonFace P (d + 1 - 2), v ∈ S.val.val → ((φ S).val ≤ G ↔ S.val ≤ F))) ∧
    (∀ (u w : Fin (d + 1) → ℝ) (G_u G_w : PolytopeFace Q),
      (G_u.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ G_u.val).direction = d) →
      (G_w.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ G_w.val).direction = d) →
      (∀ S : SkeletonFace P (d + 1 - 2), u ∈ S.val.val → ((φ S).val ≤ G_u ↔ S.val ≤ F)) →
      (∀ S : SkeletonFace P (d + 1 - 2), w ∈ S.val.val → ((φ S).val ≤ G_w ↔ S.val ≤ F)) →
      ∀ R₁ R₂ : SkeletonFace P (d + 1 - 2),
        R₁.val ≤ F → R₂.val ≤ F →
        u ∈ R₁.val.val → w ∈ R₁.val.val →
        u ∈ R₂.val.val → w ∈ R₂.val.val →
        ((φ R₁).val.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ (φ R₁).val.val).direction = d - 1) →
        ((φ R₂).val.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ (φ R₂).val.val).direction = d - 1) →
        R₁ ≠ R₂ →
        G_u = G_w) := by sorry

end Grunbaum2003
