-- Prove2me | Theorems.Thm_Grunbaum2003_simplicial_half_skeleton_dim_and_downSet_image
-- name    : Grunbaum2003.simplicial_half_skeleton_dim_and_downSet_image
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-31T22:21:39.465046+00:00
-- url     : https://prove2.me/theorems/a4f04d32-9fd9-4d8d-a7e7-140c71e85217
-- title:
--   Dimensional unambiguity and $\lfloor d/2 \rfloor$-skeleton down-set correspondence for simplicial polytopes
-- statement:
--   This lemma states the dimensional unambiguity (Grünbaum Theorem 12.2.1) and the $\lfloor d/2 \rfloor$-skeleton down-set correspondence (Perles / Dancis, Grünbaum §12.4) for simplicial $d$-polytopes.
--
--   Let $P \subseteq \mathbb{R}^d$ be a simplicial $d$-polytope (`IsSimplicialDPolytope P`), let $Q \subseteq \mathbb{R}^e$ be an arbitrary $e$-polytope (`IsDPolytope Q`), and let
--
--   $$
--   \varphi : \operatorname{skel}_{\lfloor d/2 \rfloor}(P) \xrightarrow{\;\sim\;} \operatorname{skel}_{\lfloor d/2 \rfloor}(Q)
--   $$
--
--   be an order isomorphism between their $\lfloor d/2 \rfloor$-skeletons. Then $e = d$, and every face of $P$ (respectively $Q$) has a partner in $\mathcal{F}(Q)$ (respectively $\mathcal{F}(P)$) with matching $\lfloor d/2 \rfloor$-skeleton principal down-set under $\varphi$:
--
--   $$
--   e = d \;\land\; \Bigl(\forall F \in \mathcal{F}(P),\; \exists G \in \mathcal{F}(Q),\; \forall T \in \operatorname{skel}_{\lfloor d/2 \rfloor}(Q),\; T \le G \iff \varphi^{-1}(T) \le F\Bigr) \;\land\; \Bigl(\forall G \in \mathcal{F}(Q),\; \exists F \in \mathcal{F}(P),\; \forall S \in \operatorname{skel}_{\lfloor d/2 \rfloor}(P),\; S \le F \iff \varphi(S) \le G\Bigr).
--   $$
--
--   Feeding the down-set correspondence into `skeleton_orderIso_extends_of_downSet_image` immediately constructs the global order isomorphism $\Phi : \mathcal{F}(P) \xrightarrow{\sim} \mathcal{F}(Q)$ extending $\varphi$.
--
--   **Formalization Note** Every proper face of a simplicial $d$-polytope is a simplex, so a facet $F$ of $P$ is a $(d-1)$-simplex whose $\lfloor d/2 \rfloor$-skeleton is the complete $(\lfloor d/2 \rfloor + 1)$-uniform hypergraph on its $d$ vertices.
-- source:
--   Grünbaum 2003, Convex Polytopes (2nd ed., Graduate Texts in Mathematics 221), §12.2 (Theorem 12.2.1, p. 227) & §12.4 (“Simplicial polytopes”, p. 234a)

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_SkeletonFace

set_option autoImplicit false

namespace Grunbaum2003

theorem simplicial_half_skeleton_dim_and_downSet_image (d e : ℕ)
    (P : Set (Fin d → ℝ)) (Q : Set (Fin e → ℝ))
    (hP : IsSimplicialDPolytope P) (hQ : IsDPolytope Q)
    (φ : SkeletonFace P (d / 2) ≃o SkeletonFace Q (d / 2)) :
    e = d ∧
    (∀ F : PolytopeFace P, ∃ G : PolytopeFace Q,
      ∀ T : SkeletonFace Q (d / 2), T.val ≤ G ↔ (φ.symm T).val ≤ F) ∧
    (∀ G : PolytopeFace Q, ∃ F : PolytopeFace P,
      ∀ S : SkeletonFace P (d / 2), S.val ≤ F ↔ (φ S).val ≤ G) := by sorry

end Grunbaum2003
