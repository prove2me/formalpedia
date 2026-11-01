-- Prove2me | Theorems.Thm_Grunbaum2003_blind_mani_simple_one_skeleton_downSet_image
-- name    : Grunbaum2003.blind_mani_simple_one_skeleton_downSet_image
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-31T22:21:37.247236+00:00
-- url     : https://prove2.me/theorems/0566f020-e3a0-4683-b8fb-70f621ab51cd
-- title:
--   Blind–Mani $1$-skeleton down-set correspondence for simple $d$-polytopes ($d \ge 3$)
-- statement:
--   This lemma isolates the $1$-skeleton down-set correspondence of the Blind–Mani–Walkup theorem in dimensions $d \ge 3$: for a simple $d$-polytope $P$ and any $d$-polytope $Q$ with order-isomorphic $1$-skeleton $\operatorname{skel}_1(P) \simeq_{\mathrm{ord}} \operatorname{skel}_1(Q)$, the $1$-skeleton principal down-sets of faces of $P$ and $Q$ correspond bijectively under $\varphi$.
--
--   Let $d \ge 3$ be an integer, let $P, Q \subseteq \mathbb{R}^d$ be $d$-polytopes (`IsDPolytope P`, `IsDPolytope Q`), suppose $P$ is simple in the sense that every vertex $v$ of $P$ has degree $d$ in the $1$-skeleton graph $G(P)$ (`((polytopeGraph P).neighborSet v).ncard = d`), and let
--
--   $$
--   \varphi : \operatorname{skel}_1(P) \xrightarrow{\;\sim\;} \operatorname{skel}_1(Q)
--   $$
--
--   be an order isomorphism of their $1$-skeletons. Then:
--
--   1. For every exposed face $F \in \mathcal{F}(P)$, there exists $G \in \mathcal{F}(Q)$ such that $T \le G \iff \varphi^{-1}(T) \le F$ for all $T \in \operatorname{skel}_1(Q)$; and
--   2. For every exposed face $G \in \mathcal{F}(Q)$, there exists $F \in \mathcal{F}(P)$ such that $S \le F \iff \varphi(S) \le G$ for all $S \in \operatorname{skel}_1(P)$.
--
--   Together with `skeleton_orderIso_extends_of_le_succ` (which handles $d \le 2$) and `skeleton_orderIso_extends_of_downSet_image` (which constructs the global face-lattice isomorphism from the down-set correspondence), this lemma implies `blind_mani_graph_reconstruction`.
--
--   **Formalization Note** Restricting this lemma to $d \ge 3$ separates the genuinely $3$- and higher-dimensional shellability/acyclic-orientation argument of Blind–Mani (1987) and Kalai (1988) from the low-dimensional case $d \le 2$, where $\operatorname{skel}_1(P)$ already contains all proper faces.
-- source:
--   Grünbaum 2003, Convex Polytopes (2nd ed., Graduate Texts in Mathematics 221), §12.4 (“Simple polytopes”), p. 234a

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_SkeletonFace
import Definitions.Def_Grunbaum2003_PolytopeVertex
import Definitions.Def_Grunbaum2003_polytopeGraph

set_option autoImplicit false

namespace Grunbaum2003

theorem blind_mani_simple_one_skeleton_downSet_image (d : ℕ) (hd : 3 ≤ d)
    (P Q : Set (Fin d → ℝ)) (hP : IsDPolytope P) (hQ : IsDPolytope Q)
    (hSimple : ∀ v : PolytopeVertex P,
      ((polytopeGraph P).neighborSet v).ncard = d)
    (φ : SkeletonFace P 1 ≃o SkeletonFace Q 1) :
    (∀ F : PolytopeFace P, ∃ G : PolytopeFace Q,
      ∀ T : SkeletonFace Q 1, T.val ≤ G ↔ (φ.symm T).val ≤ F) ∧
    (∀ G : PolytopeFace Q, ∃ F : PolytopeFace P,
      ∀ S : SkeletonFace P 1, S.val ≤ F ↔ (φ S).val ≤ G) := by sorry

end Grunbaum2003
