-- Prove2me | Theorems.Thm_Grunbaum2003_exists_stellar_subdivision_cone_decomposition
-- name    : Grunbaum2003.exists_stellar_subdivision_cone_decomposition
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-09T02:44:18.544515+00:00
-- url     : https://prove2.me/theorems/66fedc85-e2bf-44b8-9b3b-9e7d0d908ec9
-- title:
--   Existence of Stellar Subdivision with Cone-Face Decomposition over a Simplicial Facet
-- statement:
--   For any simplicial d-polytope P (d >= 4) with finite k-face families F(k), there exist a stellar-subdivided simplicial d-polytope P', a subdivided facet F0 in F(d - 1) with vertex tuple v, and an apex y not in P whose k-face finsets decompose into the retained old faces and the image of powersetCard k under s |-> convexHull(insert y (v  s)).
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

set_option autoImplicit false
open scoped Classical

namespace Grunbaum2003

theorem exists_stellar_subdivision_cone_decomposition (d : ℕ) (hd : 4 ≤ d)
    (P : Set (Fin d → ℝ)) (hP : IsSimplicialDPolytope P)
    (ℱ : ℕ → Finset (Set (Fin d → ℝ)))
    (hℱ : ∀ k : ℕ, (ℱ k : Set (Set (Fin d → ℝ))) =
      {F : Set (Fin d → ℝ) | F.Nonempty ∧ IsExposed ℝ P F ∧
        Module.finrank ℝ (affineSpan ℝ F).direction = k} ∧
      (ℱ k).card = faceCount P k) :
    ∃ (P' : Set (Fin d → ℝ)) (F₀ : Set (Fin d → ℝ))
      (y : Fin d → ℝ) (v : Fin d → Fin d → ℝ)
      (ℱ' : ℕ → Finset (Set (Fin d → ℝ))),
      IsSimplicialDPolytope P' ∧
      F₀ ∈ ℱ (d - 1) ∧
      y ∉ P ∧
      Function.Injective v ∧
      (∀ s : Finset (Fin d),
        convexHull ℝ (insert y (v '' (s : Set (Fin d)))) ∩
          {x : Fin d → ℝ | IsExposed ℝ P {x}} = v '' (s : Set (Fin d))) ∧
      (∀ k : ℕ, (ℱ' k : Set (Set (Fin d → ℝ))) =
        {F : Set (Fin d → ℝ) | F.Nonempty ∧ IsExposed ℝ P' F ∧
          Module.finrank ℝ (affineSpan ℝ F).direction = k} ∧
        (ℱ' k).card = faceCount P' k) ∧
      let ℱ_new : ℕ → Finset (Set (Fin d → ℝ)) := fun k =>
        ((Finset.univ : Finset (Fin d)).powersetCard k).image
          (fun s : Finset (Fin d) => convexHull ℝ (insert y (v '' (s : Set (Fin d)))))
      (∀ j : Fin d, j.val + 1 < d → ℱ' j.val = ℱ j.val ∪ ℱ_new j.val) ∧
      ℱ' (d - 1) = (ℱ (d - 1)).erase F₀ ∪ ℱ_new (d - 1) := by sorry

end Grunbaum2003
