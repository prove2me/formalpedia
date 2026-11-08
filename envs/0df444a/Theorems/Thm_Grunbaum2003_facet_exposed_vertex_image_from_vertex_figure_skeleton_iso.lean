-- Prove2me | Theorems.Thm_Grunbaum2003_facet_exposed_vertex_image_from_vertex_figure_skeleton_iso
-- name    : Grunbaum2003.facet_exposed_vertex_image_from_vertex_figure_skeleton_iso
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-08T02:14:55.090206+00:00
-- url     : https://prove2.me/theorems/df3cbbc1-8169-4de4-817f-f3bbb6aff978
-- title:
--   Target face realizing the $\varphi$-image of exposed vertices of a facet from edge preservation and vertex-figure skeleton isomorphisms ($d \ge 3$)
-- statement:
--   Given the exposed-vertex hull representations `hHullP`, `hHullQ`, the prescribed vertex-figure hyperplane cut packages `hCutP`, `hCutQ`, order-theoretic preservation of empty faces, singleton exposed vertices, and $1$-dimensional exposed edges (`hEmpty`, `hMapVert`, `hEdgeIso`), and the coordinate vertex-figure $(e-1)$-polytope and upper-interval skeleton isomorphism constructor `hVertFigSkel` (`{G ∈ PolytopeFace R | v ∈ G} ≃o PolytopeFace Q₀` restricting to `{S ∈ SkeletonFace R (k+1) | v ∈ S} ≃o SkeletonFace Q₀ k`), for any facet $F \in \mathcal{F}(P)$ containing an exposed vertex $v \in F$, there exists an exposed face $G \in \mathcal{F}(Q)$ containing precisely the $\varphi$-images of the exposed vertices of $F$.
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

theorem facet_exposed_vertex_image_from_vertex_figure_skeleton_iso (d : ℕ) (hd : 3 ≤ d)
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
    (hEdgeIso : ∀ {e f k l : ℕ} {R : Set (Fin e → ℝ)} {S : Set (Fin f → ℝ)},
      ({x : Fin e → ℝ | IsExposed ℝ R {x}}.Finite ∧
        ∀ E : PolytopeFace R,
          E.val = convexHull ℝ (E.val ∩ {x : Fin e → ℝ | IsExposed ℝ R {x}})) →
      ({y : Fin f → ℝ | IsExposed ℝ S {y}}.Finite ∧
        ∀ E : PolytopeFace S,
          E.val = convexHull ℝ (E.val ∩ {y : Fin f → ℝ | IsExposed ℝ S {y}})) →
      ∀ (ψ : SkeletonFace R k ≃o SkeletonFace S l) (T : SkeletonFace R k),
        ((ψ T).val.val.Nonempty ∧
          Module.finrank ℝ (affineSpan ℝ (ψ T).val.val).direction = 1) ↔
        (T.val.val.Nonempty ∧
          Module.finrank ℝ (affineSpan ℝ T.val.val).direction = 1))
    (hVertFigSkel : ∀ (e : ℕ), 0 < e → ∀ (R : Set (Fin e → ℝ)), IsDPolytope R →
      ({x : Fin e → ℝ | IsExposed ℝ R {x}}.Finite ∧
        ∀ E : PolytopeFace R,
          E.val = convexHull ℝ (E.val ∩ {x : Fin e → ℝ | IsExposed ℝ R {x}})) →
      ((∀ v : Fin e → ℝ, IsExposed ℝ R {v} →
          ∃ (l : StrongDual ℝ (Fin e → ℝ)) (α : ℝ),
            α < l v ∧ (∀ x ∈ R, l x ≤ l v) ∧
            ∀ w : Fin e → ℝ, IsExposed ℝ R {w} → w ≠ v →
              l w < α ∧ ∃ t : ℝ, 0 < t ∧ t < 1 ∧ l (AffineMap.lineMap v w t) = α) ∧
        (∀ (v : Fin e → ℝ) (l : StrongDual ℝ (Fin e → ℝ)) (α : ℝ),
          α < l v →
          (∀ w : Fin e → ℝ, IsExposed ℝ R {w} → w ≠ v → l w < α) →
          ∀ (G : Set (Fin e → ℝ)), IsExposed ℝ R G → v ∈ G →
            affineSpan ℝ (insert v (G ∩ l ⁻¹' {α})) = affineSpan ℝ G ∧
            ((G ∩ l ⁻¹' {α}).Nonempty ↔ G ≠ {v}) ∧
            (G ≠ {v} →
              (G ∩ l ⁻¹' {α}).Nonempty ∧
                Module.finrank ℝ (affineSpan ℝ G).direction =
                  Module.finrank ℝ (affineSpan ℝ (G ∩ l ⁻¹' {α})).direction + 1))) →
      ∀ (v : Fin e → ℝ), IsExposed ℝ R {v} →
        ∃ (l : StrongDual ℝ (Fin e → ℝ)) (α : ℝ)
          (Q₀ : Set (Fin (e - 1) → ℝ))
          (f : (Fin (e - 1) → ℝ) →ᵃ[ℝ] (Fin e → ℝ))
          (Ψ : {G : PolytopeFace R // v ∈ G.val} ≃o PolytopeFace Q₀),
          α < l v ∧
          (∀ w : Fin e → ℝ, IsExposed ℝ R {w} → w ≠ v → l w < α) ∧
          IsDPolytope Q₀ ∧
          Function.Injective f ∧
          f '' Q₀ = R ∩ l ⁻¹' {α} ∧
          (∀ G : {G : PolytopeFace R // v ∈ G.val},
            f '' (Ψ G).val = G.val.val ∩ (R ∩ l ⁻¹' {α}) ∧
            ((Ψ G).val = ∅ ↔ G.val.val = {v}) ∧
            (G.val.val ≠ {v} →
              (Ψ G).val.Nonempty ∧
                Module.finrank ℝ (affineSpan ℝ G.val.val).direction =
                  Module.finrank ℝ (affineSpan ℝ (Ψ G).val).direction + 1)) ∧
          (∀ k : ℕ,
            ∃ Ψ_skel : {S : SkeletonFace R (k + 1) // v ∈ S.val.val} ≃o
                SkeletonFace Q₀ k,
              ∀ S : {S : SkeletonFace R (k + 1) // v ∈ S.val.val},
                (Ψ_skel S).val = Ψ ⟨S.val.val, S.property⟩))
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
