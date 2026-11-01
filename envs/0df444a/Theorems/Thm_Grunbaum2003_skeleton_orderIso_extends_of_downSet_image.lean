-- Prove2me | Theorems.Thm_Grunbaum2003_skeleton_orderIso_extends_of_downSet_image
-- name    : Grunbaum2003.skeleton_orderIso_extends_of_downSet_image
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-31T22:14:30.241624+00:00
-- url     : https://prove2.me/theorems/a24960cb-444f-459a-946d-bd4ffd7c95b1
-- title:
--   Extension criterion for $k$-skeleton order isomorphisms via principal down-sets
-- statement:
--   This theorem provides the general order-theoretic and geometric criterion for extending an isomorphism between the $k$-skeletons of two polytopes to an isomorphism of their full face lattices.
--
--   Let $P \subseteq \mathbb{R}^d$ be a $d$-polytope and $Q \subseteq \mathbb{R}^e$ be an $e$-polytope, let $k \ge 0$ be a skeleton dimension, and let
--
--   $$
--   \varphi : \operatorname{skel}_k(P) \xrightarrow{\;\sim\;} \operatorname{skel}_k(Q)
--   $$
--
--   be an order isomorphism between their $k$-skeletons. Suppose that for every face $F \in \mathcal{F}(P)$ there exists a face $G \in \mathcal{F}(Q)$ whose $k$-skeleton principal down-set is the image under $\varphi$ of the $k$-skeleton principal down-set of $F$, and symmetrically for every face $G \in \mathcal{F}(Q)$:
--
--   $$
--   \forall F \in \mathcal{F}(P),\; \exists G \in \mathcal{F}(Q),\; \forall T \in \operatorname{skel}_k(Q),\quad T \le G \iff \varphi^{-1}(T) \le F,
--   $$
--
--   $$
--   \forall G \in \mathcal{F}(Q),\; \exists F \in \mathcal{F}(P),\; \forall S \in \operatorname{skel}_k(P),\quad S \le F \iff \varphi(S) \le G.
--   $$
--
--   Then there exists a global order isomorphism $\Phi : \mathcal{F}(P) \xrightarrow{\sim} \mathcal{F}(Q)$ extending $\varphi$, meaning that $\Phi(F) = \varphi(F)$ for all $F \in \operatorname{skel}_k(P)$.
--
--   Because every face of a polytope is the convex hull of its exposed vertices (which belong to $\operatorname{skel}_0(P) \subseteq \operatorname{skel}_k(P)$ for every $k \ge 0$), each face is uniquely determined by its $k$-skeleton down-set. This theorem reduces skeleton reconstruction theorems (such as $d \le k+1$, Perles's $\lfloor d/2 \rfloor$-skeleton theorem, Blind–Mani graph reconstruction, Dancis's simplicial skeleton reconstruction, and zonotope graph reconstruction) to verifying that higher-dimensional faces have matching $k$-skeleton down-sets.
--
--   **Formalization Note** The $k$-skeleton poset `SkeletonFace P k` is the subposet of `PolytopeFace P` consisting of $\emptyset$ and all exposed faces of affine dimension at most $k$.
-- source:
--   Grünbaum 2003, Convex Polytopes (2nd ed., Graduate Texts in Mathematics 221), §12.1–12.3, pp. 225–231, Theorem 12.1.1

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_SkeletonFace

set_option autoImplicit false

namespace Grunbaum2003

theorem skeleton_orderIso_extends_of_downSet_image (d e k : ℕ)
    (P : Set (Fin d → ℝ)) (Q : Set (Fin e → ℝ))
    (hP : IsDPolytope P) (hQ : IsDPolytope Q)
    (φ : SkeletonFace P k ≃o SkeletonFace Q k)
    (hFwd : ∀ F : PolytopeFace P, ∃ G : PolytopeFace Q,
      ∀ T : SkeletonFace Q k, T.val ≤ G ↔ (φ.symm T).val ≤ F)
    (hBwd : ∀ G : PolytopeFace Q, ∃ F : PolytopeFace P,
      ∀ S : SkeletonFace P k, S.val ≤ F ↔ (φ S).val ≤ G) :
    ∃ Φ : PolytopeFace P ≃o PolytopeFace Q,
      ∀ F : SkeletonFace P k, Φ F.val = (φ F).val := by sorry

end Grunbaum2003
