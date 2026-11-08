-- Prove2me | Theorems.Thm_Grunbaum2003_facet_codim_two_skeleton_downSet_of_vertex_figure_cut
-- name    : Grunbaum2003.facet_codim_two_skeleton_downSet_of_vertex_figure_cut
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-07T19:08:51.786643+00:00
-- url     : https://prove2.me/theorems/5c64d98b-9f9a-4b5c-a133-9b934d5d0d84
-- title:
--   Inductive $(d-2)$-skeleton facet down-set correspondence from prescribed vertex-figure hyperplane cuts ($d \ge 3$)
-- statement:
--   This lemma states the inductive vertex-figure gluing step of Grünbaum's Theorem 12.3.1 (`facet_codim_two_skeleton_downSet_image`) in dimensions $d \ge 3$, given:
--   - the finite exposed-vertex hull representations $E = \operatorname{conv}(E \cap \operatorname{vert}(P))$ and $E = \operatorname{conv}(E \cap \operatorname{vert}(Q))$ from `polytope_face_eq_convexHull_exposed_vertices`;
--   - the prescribed vertex-figure hyperplane cut and affine dimension-shift packages $\dim(\operatorname{aff} G) = \dim(\operatorname{aff}(G \cap l^{-1}(\{\alpha\}))) + 1$ for both $P$ and $Q$ from `vertex_figure_face_finrank_and_prescribed_cut`; and
--   - an exposed vertex $v \in F \cap \operatorname{vert}(P)$ of the given facet $F \subseteq P$.
--
--   Under these hypotheses, for any order isomorphism $\varphi : \operatorname{skel}_{d-2}(P) \xrightarrow{\sim} \operatorname{skel}_{d-2}(Q)$, there exists an exposed face $G \in \mathcal{F}(Q)$ whose $(d-2)$-skeleton principal down-set matches the $\varphi$-image of the $(d-2)$-skeleton principal down-set of $F$.
-- source:
--   Grünbaum 2003, Convex Polytopes (2nd ed., Graduate Texts in Mathematics 221), §12.3, pp. 228–231, Theorem 12.3.1

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

theorem facet_codim_two_skeleton_downSet_of_vertex_figure_cut (d : ℕ) (hd : 3 ≤ d)
    (P Q : Set (Fin d → ℝ)) (hP : IsDPolytope P) (hQ : IsDPolytope Q)
    (hHullP : {x : Fin d → ℝ | IsExposed ℝ P {x}}.Finite ∧
      ∀ E : PolytopeFace P, E.val = convexHull ℝ (E.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}}))
    (hHullQ : {x : Fin d → ℝ | IsExposed ℝ Q {x}}.Finite ∧
      ∀ E : PolytopeFace Q, E.val = convexHull ℝ (E.val ∩ {x : Fin d → ℝ | IsExposed ℝ Q {x}}))
    (hCutP :
      (∀ v : Fin d → ℝ, IsExposed ℝ P {v} →
        ∃ (l : StrongDual ℝ (Fin d → ℝ)) (α : ℝ),
          α < l v ∧ (∀ x ∈ P, l x ≤ l v) ∧
          ∀ w : Fin d → ℝ, IsExposed ℝ P {w} → w ≠ v →
            l w < α ∧ ∃ t : ℝ, 0 < t ∧ t < 1 ∧ l (AffineMap.lineMap v w t) = α) ∧
      (∀ (v : Fin d → ℝ) (l : StrongDual ℝ (Fin d → ℝ)) (α : ℝ),
        α < l v →
        (∀ w : Fin d → ℝ, IsExposed ℝ P {w} → w ≠ v → l w < α) →
        ∀ (G : Set (Fin d → ℝ)), IsExposed ℝ P G → v ∈ G →
          affineSpan ℝ (insert v (G ∩ l ⁻¹' {α})) = affineSpan ℝ G ∧
          ((G ∩ l ⁻¹' {α}).Nonempty ↔ G ≠ {v}) ∧
          (G ≠ {v} →
            (G ∩ l ⁻¹' {α}).Nonempty ∧
              Module.finrank ℝ (affineSpan ℝ G).direction =
                Module.finrank ℝ (affineSpan ℝ (G ∩ l ⁻¹' {α})).direction + 1)))
    (hCutQ :
      (∀ v : Fin d → ℝ, IsExposed ℝ Q {v} →
        ∃ (l : StrongDual ℝ (Fin d → ℝ)) (α : ℝ),
          α < l v ∧ (∀ x ∈ Q, l x ≤ l v) ∧
          ∀ w : Fin d → ℝ, IsExposed ℝ Q {w} → w ≠ v →
            l w < α ∧ ∃ t : ℝ, 0 < t ∧ t < 1 ∧ l (AffineMap.lineMap v w t) = α) ∧
      (∀ (v : Fin d → ℝ) (l : StrongDual ℝ (Fin d → ℝ)) (α : ℝ),
        α < l v →
        (∀ w : Fin d → ℝ, IsExposed ℝ Q {w} → w ≠ v → l w < α) →
        ∀ (G : Set (Fin d → ℝ)), IsExposed ℝ Q G → v ∈ G →
          affineSpan ℝ (insert v (G ∩ l ⁻¹' {α})) = affineSpan ℝ G ∧
          ((G ∩ l ⁻¹' {α}).Nonempty ↔ G ≠ {v}) ∧
          (G ≠ {v} →
            (G ∩ l ⁻¹' {α}).Nonempty ∧
              Module.finrank ℝ (affineSpan ℝ G).direction =
                Module.finrank ℝ (affineSpan ℝ (G ∩ l ⁻¹' {α})).direction + 1)))
    (φ : SkeletonFace P (d - 2) ≃o SkeletonFace Q (d - 2))
    (F : PolytopeFace P)
    (hFacet : F.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ F.val).direction = d - 1)
    (v : Fin d → ℝ) (hv : IsExposed ℝ P {v}) (hvF : v ∈ F.val) :
    ∃ G : PolytopeFace Q,
      ∀ T : SkeletonFace Q (d - 2), T.val ≤ G ↔ (φ.symm T).val ≤ F := by sorry

end Grunbaum2003
