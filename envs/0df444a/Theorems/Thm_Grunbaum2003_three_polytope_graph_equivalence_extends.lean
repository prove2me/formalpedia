-- Prove2me | Theorems.Thm_Grunbaum2003_three_polytope_graph_equivalence_extends
-- name    : Grunbaum2003.three_polytope_graph_equivalence_extends
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-08T20:52:09.253149+00:00
-- url     : https://prove2.me/theorems/aa3f1f31-1cd4-458b-bda3-7ebff35c971a
-- title:
--   Theorem 12.3.1 for $d=3$: every graph equivalence of $3$-polytopes extends to the face lattices
-- statement:
--   Let $P,Q\subseteq\mathbb R^3$ be $3$-polytopes and let
--
--   $$
--   \varphi:\operatorname{skel}_1(P)\xrightarrow{\ \sim\ }\operatorname{skel}_1(Q)
--   $$
--
--   be an isomorphism of their $1$-skeleta, i.e. an inclusion-preserving bijection between the posets consisting of the empty face, the vertices and the edges. Then $\varphi$ extends to an isomorphism $\Phi$ of the full face lattices of $P$ and $Q$.
--
--   This is the case $d=3$ of Grünbaum's Theorem 12.3.1: the graph of a $3$-polytope determines its face lattice, and every graph isomorphism is induced by a combinatorial equivalence. Equivalently, the facets of a $3$-polytope are exactly the induced non-separating cycles of its graph (Whitney). This case is the base of the induction on $d$ for Theorem 12.3.1.
--
--   **Formalization Note** Polytopes are full-dimensional finite convex hulls in `Fin d → ℝ`. `PolytopeFace P` is the poset of all exposed faces of $P$ (including $\emptyset$ and $P$), ordered by inclusion, and `SkeletonFace P k` is its sub-poset of faces that are empty or have dimension at most $k$.
-- source:
--   Branko Grünbaum, Convex Polytopes, 2nd ed. (Springer GTM 221, 2003), §12.3, Theorem 12.3.1, printed p. 228 / PDF p. 270, case d = 3 (face-lattice formulation p. 231 / PDF p. 273); cf. H. Whitney, Congruent graphs and the connectivity of graphs, Amer. J. Math. 54 (1932)

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_SkeletonFace

set_option autoImplicit false

namespace Grunbaum2003

theorem three_polytope_graph_equivalence_extends
    (P Q : Set (Fin 3 → ℝ)) (hP : IsDPolytope P) (hQ : IsDPolytope Q)
    (φ : SkeletonFace P 1 ≃o SkeletonFace Q 1) :
    ∃ Φ : PolytopeFace P ≃o PolytopeFace Q,
      ∀ F : SkeletonFace P 1, Φ F.val = (φ F).val := by sorry

end Grunbaum2003
