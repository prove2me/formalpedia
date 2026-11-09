-- Prove2me | Theorems.Thm_Grunbaum2003_exists_stellar_subdivision_face_finset_bijection
-- name    : Grunbaum2003.exists_stellar_subdivision_face_finset_bijection
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-09T02:23:33.5102+00:00
-- url     : https://prove2.me/theorems/78c0415b-cc84-4323-a195-9e5f659d5db2
-- title:
--   Existence of Stellar Subdivision with Subface Finset Bijections to Fin d Subsets
-- statement:
--   Given the finite k-face families of a simplicial d-polytope P (d >= 4), there exist a stellar-subdivided simplicial d-polytope P', a subdivided facet F0, and new j-face finsets disjoint from the retained old j-faces and in bijection with the j-element subsets of Fin d.
-- source:
--   Grünbaum, Convex Polytopes (2003), Ch. 10

import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

set_option autoImplicit false
open scoped Classical

namespace Grunbaum2003

theorem exists_stellar_subdivision_face_finset_bijection (d : ℕ) (hd : 4 ≤ d)
    (P : Set (Fin d → ℝ)) (hP : IsSimplicialDPolytope P)
    (ℱ : ℕ → Finset (Set (Fin d → ℝ)))
    (hℱ : ∀ k : ℕ, (ℱ k : Set (Set (Fin d → ℝ))) =
      {F : Set (Fin d → ℝ) | F.Nonempty ∧ IsExposed ℝ P F ∧
        Module.finrank ℝ (affineSpan ℝ F).direction = k} ∧
      (ℱ k).card = faceCount P k) :
    ∃ (P' : Set (Fin d → ℝ)) (F₀ : Set (Fin d → ℝ))
      (ℱ' ℱ_new : ℕ → Finset (Set (Fin d → ℝ))),
      IsSimplicialDPolytope P' ∧
      F₀ ∈ ℱ (d - 1) ∧
      (∀ k : ℕ, (ℱ' k : Set (Set (Fin d → ℝ))) =
        {F : Set (Fin d → ℝ) | F.Nonempty ∧ IsExposed ℝ P' F ∧
          Module.finrank ℝ (affineSpan ℝ F).direction = k} ∧
        (ℱ' k).card = faceCount P' k) ∧
      (∀ j : Fin d, j.val + 1 < d →
        ℱ' j.val = ℱ j.val ∪ ℱ_new j.val ∧
        Disjoint (ℱ j.val) (ℱ_new j.val) ∧
        Nonempty (ℱ_new j.val ≃ (Finset.univ : Finset (Fin d)).powersetCard j.val)) ∧
      (ℱ' (d - 1) = (ℱ (d - 1)).erase F₀ ∪ ℱ_new (d - 1) ∧
        Disjoint ((ℱ (d - 1)).erase F₀) (ℱ_new (d - 1)) ∧
        Nonempty (ℱ_new (d - 1) ≃ (Finset.univ : Finset (Fin d)).powersetCard (d - 1))) := by sorry

end Grunbaum2003
