-- Prove2me | Theorems.Thm_Grunbaum2003_facet_exposed_vertex_image_of_vertex_figure_cut
-- name    : Grunbaum2003.facet_exposed_vertex_image_of_vertex_figure_cut
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-08T01:30:23.062142+00:00
-- url     : https://prove2.me/theorems/867c690e-5ca2-43df-8e85-1088d4ac3e84
-- title:
--   Target face realizing the $\varphi$-image of exposed vertices of a facet from vertex-figure cuts ($d \ge 3$)
-- statement:
--   Given the exposed-vertex hull representations `hHullP`, `hHullQ`, the prescribed vertex-figure hyperplane cut and affine dimension-shift packages `hCutP`, `hCutQ`, and the proved order-theoretic preservation of empty faces and singleton exposed vertices (`hEmpty`, `hMapVert`) under $\varphi : \operatorname{SkeletonFace} P (d - 2) \xrightarrow{\sim} \operatorname{SkeletonFace} Q (d - 2)$, for any facet $F \in \mathcal{F}(P)$ containing an exposed vertex $v \in F$, there exists an exposed face $G \in \mathcal{F}(Q)$ containing precisely the $\varphi$-images of the exposed vertices of $F$:
--   $$
--   \forall x \in \operatorname{vert}(P),\quad \varphi(\{x\}).\mathrm{val} \le G \iff x \in F.\mathrm{val}.
--   $$
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

theorem facet_exposed_vertex_image_of_vertex_figure_cut (d : ℕ) (hd : 3 ≤ d)
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
    (vertexSkeletonFace : ∀ {e : ℕ} (R : Set (Fin e → ℝ)) (k : ℕ)
      (x : Fin e → ℝ), IsExposed ℝ R {x} → SkeletonFace R k)
    (hVertexVal : ∀ {e : ℕ} (R : Set (Fin e → ℝ)) (k : ℕ) (x : Fin e → ℝ) (hx : IsExposed ℝ R {x}),
      (vertexSkeletonFace R k x hx).val.val = {x})
    (φ : SkeletonFace P (d - 2) ≃o SkeletonFace Q (d - 2))
    (hEmpty : ∀ S : SkeletonFace P (d - 2), (φ S).val.val = ∅ ↔ S.val.val = ∅)
    (hMapVert : ∀ (x : Fin d → ℝ) (hx : IsExposed ℝ P {x}),
      ∃ (y : Fin d → ℝ) (hy : IsExposed ℝ Q {y}),
        φ (vertexSkeletonFace P (d - 2) x hx) = vertexSkeletonFace Q (d - 2) y hy)
    (F : PolytopeFace P)
    (hFacet : F.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ F.val).direction = d - 1)
    (v : Fin d → ℝ) (hv : IsExposed ℝ P {v}) (hvF : v ∈ F.val) :
    ∃ G : PolytopeFace Q,
      ∀ (x : Fin d → ℝ) (hx : IsExposed ℝ P {x}),
        (φ (vertexSkeletonFace P (d - 2) x hx)).val ≤ G ↔ x ∈ F.val := by sorry

end Grunbaum2003
