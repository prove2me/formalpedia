-- Prove2me | Theorems.Thm_Grunbaum2003_facet_codim_two_skeleton_downSet_image
-- name    : Grunbaum2003.facet_codim_two_skeleton_downSet_image
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-31T22:21:35.908315+00:00
-- url     : https://prove2.me/theorems/bd2bcada-c04e-45d4-8cf3-3726c71519c3
-- title:
--   Codimension-two skeleton down-set correspondence for facets of $d$-polytopes
-- statement:
--   This lemma states the facet reconstruction step of Grünbaum's Theorem 12.3.1: under an order isomorphism between the $(d-2)$-skeletons of two $d$-polytopes in dimension $d \ge 3$, the $(d-2)$-skeleton principal down-set of every facet of $P$ corresponds under $\varphi$ to the $(d-2)$-skeleton principal down-set of an exposed face of $Q$.
--
--   Let $d \ge 3$ be an integer, let $P, Q \subseteq \mathbb{R}^d$ be $d$-polytopes (`IsDPolytope P`, `IsDPolytope Q`), and let
--
--   $$
--   \varphi : \operatorname{skel}_{d-2}(P) \xrightarrow{\;\sim\;} \operatorname{skel}_{d-2}(Q)
--   $$
--
--   be an order isomorphism between their $(d-2)$-skeletons. For every facet $F \in \mathcal{F}(P)$ (that is, a nonempty exposed face $F \subseteq P$ of affine dimension $\dim(F) = d - 1$), there exists an exposed face $G \in \mathcal{F}(Q)$ such that
--
--   $$
--   \forall T \in \operatorname{skel}_{d-2}(Q),\quad T \le G \iff \varphi^{-1}(T) \le F.
--   $$
--
--   Because every face of a $d$-polytope that is neither in $\operatorname{skel}_{d-2}(P)$ nor equal to $P$ is a facet (`polytopeFace_trichotomy_codim_two`), combining this lemma with `skeleton_orderIso_extends_of_downSet_image` yields the full extension $\Phi : \mathcal{F}(P) \xrightarrow{\sim} \mathcal{F}(Q)$ of $\varphi$.
--
--   **Formalization Note** A facet of $P$ is specified by `F.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ F.val).direction = d - 1`. Applying the lemma symmetrically to $(Q, P, \varphi^{-1})$ provides the backward down-set correspondence for facets of $Q$.
-- source:
--   Grünbaum 2003, Convex Polytopes (2nd ed., Graduate Texts in Mathematics 221), §12.3, pp. 228–231, Theorem 12.3.1

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_SkeletonFace
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

set_option autoImplicit false

namespace Grunbaum2003

theorem facet_codim_two_skeleton_downSet_image (d : ℕ) (hd : 3 ≤ d)
    (P Q : Set (Fin d → ℝ)) (hP : IsDPolytope P) (hQ : IsDPolytope Q)
    (φ : SkeletonFace P (d - 2) ≃o SkeletonFace Q (d - 2))
    (F : PolytopeFace P)
    (hFacet : F.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ F.val).direction = d - 1) :
    ∃ G : PolytopeFace Q,
      ∀ T : SkeletonFace Q (d - 2), T.val ≤ G ↔ (φ.symm T).val ≤ F := by sorry

end Grunbaum2003
