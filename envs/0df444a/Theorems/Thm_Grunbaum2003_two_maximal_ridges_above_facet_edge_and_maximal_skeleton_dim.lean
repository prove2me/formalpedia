-- Prove2me | Theorems.Thm_Grunbaum2003_two_maximal_ridges_above_facet_edge_and_maximal_skeleton_dim
-- name    : Grunbaum2003.two_maximal_ridges_above_facet_edge_and_maximal_skeleton_dim
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-08T22:02:07.867003+00:00
-- url     : https://prove2.me/theorems/3410a269-af03-4b79-8911-393cb5865c5c
-- title:
--   Two maximal skeleton ridges above every facet edge and dimension of maximal skeleton faces
-- statement:
--   Let $d \ge 3$ and let $P, Q \subseteq \mathbb{R}^{d+1}$ be $(d+1)$-polytopes, and let $F$ be a facet of $P$. Then:
--
--   1. (**Two maximal skeleton ridges above each edge of $F$**) For every exposed $1$-face $E \subseteq F$ of $P$, there exist two distinct elements $R_1 \ne R_2$ of $\operatorname{skel}_{d-1}(P)$ contained in $F$ and containing $E$ such that both $R_1$ and $R_2$ are maximal in the poset $\operatorname{skel}_{d-1}(P)$.
--
--   2. (**Maximal faces of $\operatorname{skel}_{d-1}(Q)$ are ridges**) Every maximal element $T$ of the poset $\operatorname{skel}_{d-1}(Q)$ is a nonempty exposed face of $Q$ of affine dimension $d - 1$.
--
--   **Formalization Note** Polytopes are represented by `IsDPolytope`, exposed faces by `PolytopeFace`, and the $(d-1)$-skeleton by `SkeletonFace P (d + 1 - 2)`.
-- source:
--   Branko Grünbaum, Convex Polytopes, 2nd ed. (Springer GTM 221, 2003), §3.1–3.2 and §12.3, Theorem 12.3.1, printed p. 228 / PDF p. 270

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

theorem two_maximal_ridges_above_facet_edge_and_maximal_skeleton_dim (d : ℕ) (hd : 3 ≤ d)
    (P Q : Set (Fin (d + 1) → ℝ)) (hP : IsDPolytope P) (hQ : IsDPolytope Q)
    (F : PolytopeFace P)
    (hF : F.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ F.val).direction = d) :
    (∀ (E : PolytopeFace P),
      (E.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ E.val).direction = 1) →
      E ≤ F →
      ∃ R₁ R₂ : SkeletonFace P (d + 1 - 2),
        R₁ ≠ R₂ ∧ R₁.val ≤ F ∧ R₂.val ≤ F ∧ E ≤ R₁.val ∧ E ≤ R₂.val ∧
        (∀ T : SkeletonFace P (d + 1 - 2), R₁ ≤ T → T = R₁) ∧
        (∀ T : SkeletonFace P (d + 1 - 2), R₂ ≤ T → T = R₂)) ∧
    (∀ (T : SkeletonFace Q (d + 1 - 2)),
      (∀ U : SkeletonFace Q (d + 1 - 2), T ≤ U → U = T) →
      T.val.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ T.val.val).direction = d - 1) := by sorry

end Grunbaum2003
