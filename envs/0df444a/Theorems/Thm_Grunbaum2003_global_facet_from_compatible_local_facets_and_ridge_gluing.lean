-- Prove2me | Theorems.Thm_Grunbaum2003_global_facet_from_compatible_local_facets_and_ridge_gluing
-- name    : Grunbaum2003.global_facet_from_compatible_local_facets_and_ridge_gluing
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-08T21:13:33.672946+00:00
-- url     : https://prove2.me/theorems/b094146b-2141-4b12-9f57-f95efd0a75a0
-- title:
--   Global facet image from compatible local facets and two-ridge gluing along facet edges
-- statement:
--   Let $d\ge 3$, let $P,Q\subseteq\mathbb R^{d+1}$ be $(d+1)$-polytopes, let $\varphi:\operatorname{skel}_{d-1}(P)\xrightarrow{\sim}\operatorname{skel}_{d-1}(Q)$ be an isomorphism of their $(d-1)$-skeleta, and let $F$ be a facet of $P$ (dimension $d\ge 3$). Assume:
--
--   1. Every exposed vertex $v\in F$ has a compatible local facet $G_v$ of $Q$ (of dimension $d$) such that $\varphi(S)\subseteq G_v\iff S\subseteq F$ for every $S\in\operatorname{skel}_{d-1}(P)$ containing $v$;
--   2. Whenever two vertices $u,w\in F$ lie in two distinct faces $R_1\ne R_2$ of $F$ in $\operatorname{skel}_{d-1}(P)$ whose images $\varphi(R_1),\varphi(R_2)$ have dimension $d-1$, any two compatible local facets $G_u,G_w$ at $u$ and $w$ coincide.
--
--   Then all local facets $G_v$ ($v\in F$) paste together into a single global face $G$ of $Q$ whose $(d-1)$-skeleton down-set is the image under $\varphi$ of that of $F$:
--
--   $$
--   \forall T\in\operatorname{skel}_{d-1}(Q),\qquad T\subseteq G\iff \varphi^{-1}(T)\subseteq F.
--   $$
--
--   Because $\dim F=d\ge 3$, every edge $uw$ of $F$ is contained in at least two distinct ridges $R_1,R_2$ of $F$, and the graph of $F$ is connected, so the two-ridge gluing condition propagates $G_u=G_w$ across all vertices of $F$.
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

theorem global_facet_from_compatible_local_facets_and_ridge_gluing (d : ℕ) (hd : 3 ≤ d)
    (P Q : Set (Fin (d + 1) → ℝ)) (hP : IsDPolytope P) (hQ : IsDPolytope Q)
    (φ : SkeletonFace P (d + 1 - 2) ≃o SkeletonFace Q (d + 1 - 2))
    (F : PolytopeFace P)
    (hF : F.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ F.val).direction = d)
    (hLocal : ∀ (v : Fin (d + 1) → ℝ), IsExposed ℝ P {v} → v ∈ F.val →
      ∃ G : PolytopeFace Q,
        G.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ G.val).direction = d ∧
        (∀ S : SkeletonFace P (d + 1 - 2), v ∈ S.val.val → ((φ S).val ≤ G ↔ S.val ≤ F)))
    (hGlue : ∀ (u w : Fin (d + 1) → ℝ) (G_u G_w : PolytopeFace Q),
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
        G_u = G_w) :
    ∃ G : PolytopeFace Q,
      ∀ T : SkeletonFace Q (d + 1 - 2), T.val ≤ G ↔ (φ.symm T).val ≤ F := by sorry

end Grunbaum2003
