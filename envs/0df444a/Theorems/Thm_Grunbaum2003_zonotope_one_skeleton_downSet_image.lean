-- Prove2me | Theorems.Thm_Grunbaum2003_zonotope_one_skeleton_downSet_image
-- name    : Grunbaum2003.zonotope_one_skeleton_downSet_image
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-31T22:21:43.242382+00:00
-- url     : https://prove2.me/theorems/ab101e28-e3a8-461d-9cb4-9216da9fbf67
-- title:
--   Björner–Edelman–Ziegler $1$-skeleton down-set correspondence for zonotopes ($d \ge 3$)
-- statement:
--   This lemma states the $1$-skeleton down-set correspondence of the Björner–Edelman–Ziegler theorem for $d$-dimensional zonotopes in dimensions $d \ge 3$.
--
--   Let $d \ge 3$, let $P, Q \subseteq \mathbb{R}^d$ be $d$-polytopes (`IsDPolytope P`, `IsDPolytope Q`) such that $P$ is a zonotope (`IsZonotope P`), and let
--
--   $$
--   \varphi : \operatorname{skel}_1(P) \xrightarrow{\;\sim\;} \operatorname{skel}_1(Q)
--   $$
--
--   be an order isomorphism between their $1$-skeletons. Then the $1$-skeleton principal down-sets of faces of $P$ and $Q$ correspond under $\varphi$:
--
--   $$
--   \Bigl(\forall F \in \mathcal{F}(P),\; \exists G \in \mathcal{F}(Q),\; \forall T \in \operatorname{skel}_1(Q),\; T \le G \iff \varphi^{-1}(T) \le F\Bigr) \;\land\; \Bigl(\forall G \in \mathcal{F}(Q),\; \exists F \in \mathcal{F}(P),\; \forall S \in \operatorname{skel}_1(P),\; S \le F \iff \varphi(S) \le G\Bigr).
--   $$
--
--   Combining this lemma in dimensions $d \ge 3$ with `skeleton_orderIso_extends_of_downSet_image`, and using `skeleton_orderIso_extends_of_le_succ` in dimensions $d \le 2$, yields the full face-lattice reconstruction theorem `zonotope_graph_reconstruction`.
--
--   **Formalization Note** In Lean, `IsZonotope P` asserts that $P$ is a Minkowski sum of finitely many line segments (equivalently, an affine image of a standard cube).
-- source:
--   Grünbaum 2003, Convex Polytopes (2nd ed., Graduate Texts in Mathematics 221), §12.4 (“Zonotopes”), p. 234b

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_IsZonotope
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_SkeletonFace

set_option autoImplicit false

namespace Grunbaum2003

theorem zonotope_one_skeleton_downSet_image (d : ℕ) (hd : 3 ≤ d)
    (P Q : Set (Fin d → ℝ)) (hP : IsDPolytope P) (hQ : IsDPolytope Q)
    (hZ : IsZonotope P)
    (φ : SkeletonFace P 1 ≃o SkeletonFace Q 1) :
    (∀ F : PolytopeFace P, ∃ G : PolytopeFace Q,
      ∀ T : SkeletonFace Q 1, T.val ≤ G ↔ (φ.symm T).val ≤ F) ∧
    (∀ G : PolytopeFace Q, ∃ F : PolytopeFace P,
      ∀ S : SkeletonFace P 1, S.val ≤ F ↔ (φ S).val ≤ G) := by sorry

end Grunbaum2003
