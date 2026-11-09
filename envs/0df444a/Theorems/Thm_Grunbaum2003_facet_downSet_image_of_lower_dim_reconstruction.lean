-- Prove2me | Theorems.Thm_Grunbaum2003_facet_downSet_image_of_lower_dim_reconstruction
-- name    : Grunbaum2003.facet_downSet_image_of_lower_dim_reconstruction
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-08T20:52:19.468882+00:00
-- url     : https://prove2.me/theorems/9f75fa4b-c92e-4068-a097-9d38cadef2e2
-- title:
--   Induction step for Theorem 12.3.1: facets have face images under a $(d-2)$-skeleton equivalence
-- statement:
--   Let $d\ge 3$ and assume Theorem 12.3.1 holds in dimension $d$: for all $d$-polytopes $P',Q'\subseteq\mathbb R^d$, every isomorphism $\operatorname{skel}_{d-2}(P')\cong\operatorname{skel}_{d-2}(Q')$ extends to an isomorphism of the face lattices.
--
--   Let $P,Q\subseteq\mathbb R^{d+1}$ be $(d+1)$-polytopes, let
--
--   $$
--   \varphi:\operatorname{skel}_{d-1}(P)\xrightarrow{\ \sim\ }\operatorname{skel}_{d-1}(Q)
--   $$
--
--   be an isomorphism of their $(d-1)$-skeleta, and let $F$ be a facet of $P$ (a nonempty face of dimension $d$). Then there is a face $G$ of $Q$ whose faces in the $(d-1)$-skeleton are exactly the images of the faces of $F$:
--
--   $$
--   T\subseteq G\iff\varphi^{-1}(T)\subseteq F\qquad\text{for all }T\in\operatorname{skel}_{d-1}(Q).
--   $$
--
--   This is the geometric core of the induction step in the proof of Theorem 12.3.1. At each vertex $v$ of $F$, $\varphi$ restricts to an isomorphism of the $(d-2)$-skeleta of the vertex figures at $v$ and $\varphi(v)$, and the induction hypothesis gives a facet of $Q$ at $\varphi(v)$ compatible with $F$. These local images agree along every edge of $F$, because the edge lies in two distinct ridges of $F$ and two distinct facets share at most one ridge. Connectivity of the graph of $F$ then makes them all equal to a single $G$.
--
--   **Formalization Note** Polytopes are full-dimensional finite convex hulls in `Fin d → ℝ`. `PolytopeFace P` is the poset of all exposed faces of $P$ (including $\emptyset$ and $P$), ordered by inclusion, and `SkeletonFace P k` is its sub-poset of faces that are empty or have dimension at most $k$.
-- source:
--   Branko Grünbaum, Convex Polytopes, 2nd ed. (Springer GTM 221, 2003), §12.3, Theorem 12.3.1, printed p. 228 / PDF p. 270 (induction on d via vertex figures; face-lattice formulation p. 231 / PDF p. 273)

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_SkeletonFace

set_option autoImplicit false

namespace Grunbaum2003

theorem facet_downSet_image_of_lower_dim_reconstruction (d : ℕ) (hd : 3 ≤ d)
    (ih : ∀ (P Q : Set (Fin d → ℝ)), IsDPolytope P → IsDPolytope Q →
      ∀ φ : SkeletonFace P (d - 2) ≃o SkeletonFace Q (d - 2),
        ∃ Φ : PolytopeFace P ≃o PolytopeFace Q,
          ∀ F : SkeletonFace P (d - 2), Φ F.val = (φ F).val)
    (P Q : Set (Fin (d + 1) → ℝ)) (hP : IsDPolytope P) (hQ : IsDPolytope Q)
    (φ : SkeletonFace P (d + 1 - 2) ≃o SkeletonFace Q (d + 1 - 2))
    (F : PolytopeFace P)
    (hF : F.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ F.val).direction = d) :
    ∃ G : PolytopeFace Q,
      ∀ T : SkeletonFace Q (d + 1 - 2), T.val ≤ G ↔ (φ.symm T).val ≤ F := by sorry

end Grunbaum2003
