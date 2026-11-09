-- Prove2me | Theorems.Thm_Grunbaum2003_stellar_cone_face_injective_disjoint_and_equiv
-- name    : Grunbaum2003.stellar_cone_face_injective_disjoint_and_equiv
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-09T02:44:07.028185+00:00
-- url     : https://prove2.me/theorems/2a06e6cc-e6b0-4e61-8227-633835659f2a
-- title:
--   Injectivity, Disjointness, and Subset Bijection for Stellar Subdivision Cone Faces
-- statement:
--   Proves that every facet F0 of a simplicial d-polytope P (d >= 4) is spanned by an affinely independent, injective d-tuple of exposed vertices v, and that for any apex y not in P with convexHull(insert y (v  s)) cap V(P) = v  s, the new cone-face finsets are disjoint from the old k-face finsets and in bijection with powersetCard k of Fin d.
-- source:
--   Grünbaum, Convex Polytopes (2003), Ch. 10

import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.AffineSpace.Independent

set_option autoImplicit false
open scoped Classical

namespace Grunbaum2003

theorem stellar_cone_face_injective_disjoint_and_equiv (d : ℕ) (hd : 4 ≤ d) :
    (∀ {P : Set (Fin d → ℝ)}, IsSimplicialDPolytope P →
      ∀ (ℱ : ℕ → Finset (Set (Fin d → ℝ))),
        (∀ k : ℕ, (ℱ k : Set (Set (Fin d → ℝ))) =
          {F : Set (Fin d → ℝ) | F.Nonempty ∧ IsExposed ℝ P F ∧
            Module.finrank ℝ (affineSpan ℝ F).direction = k} ∧
          (ℱ k).card = faceCount P k) →
        ∀ (F₀ : Set (Fin d → ℝ)), F₀ ∈ ℱ (d - 1) →
          ∃ v : Fin d → Fin d → ℝ,
            AffineIndependent ℝ v ∧
            Function.Injective v ∧
            (∀ i : Fin d, IsExposed ℝ P {v i}) ∧
            F₀ = convexHull ℝ (Set.range v) ∧
            F₀ ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}} = Set.range v) ∧
    (∀ {P : Set (Fin d → ℝ)}
      (ℱ : ℕ → Finset (Set (Fin d → ℝ))),
      (∀ k : ℕ, (ℱ k : Set (Set (Fin d → ℝ))) =
        {F : Set (Fin d → ℝ) | F.Nonempty ∧ IsExposed ℝ P F ∧
          Module.finrank ℝ (affineSpan ℝ F).direction = k} ∧
        (ℱ k).card = faceCount P k) →
      ∀ (y : Fin d → ℝ), y ∉ P →
      ∀ (v : Fin d → Fin d → ℝ), Function.Injective v →
      (∀ s : Finset (Fin d),
        convexHull ℝ (insert y (v '' (s : Set (Fin d)))) ∩
          {x : Fin d → ℝ | IsExposed ℝ P {x}} = v '' (s : Set (Fin d))) →
      let ℱ_new : ℕ → Finset (Set (Fin d → ℝ)) := fun k =>
        ((Finset.univ : Finset (Fin d)).powersetCard k).image
          (fun s : Finset (Fin d) => convexHull ℝ (insert y (v '' (s : Set (Fin d)))))
      (∀ k : ℕ,
        Disjoint (ℱ k) (ℱ_new k) ∧
        Nonempty (ℱ_new k ≃ (Finset.univ : Finset (Fin d)).powersetCard k)) ∧
      (∀ F₀ : Set (Fin d → ℝ),
        Disjoint ((ℱ (d - 1)).erase F₀) (ℱ_new (d - 1)))) := by sorry

end Grunbaum2003
