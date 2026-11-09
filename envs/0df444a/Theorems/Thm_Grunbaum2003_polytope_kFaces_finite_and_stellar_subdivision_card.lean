-- Prove2me | Theorems.Thm_Grunbaum2003_polytope_kFaces_finite_and_stellar_subdivision_card
-- name    : Grunbaum2003.polytope_kFaces_finite_and_stellar_subdivision_card
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-09T02:23:29.749534+00:00
-- url     : https://prove2.me/theorems/4b346646-918e-454d-82e9-fc430135fe57
-- title:
--   Finiteness of k-Face Families and Stellar Subdivision Face Counts from Subset Bijections
-- statement:
--   For any d-polytope P and dimension k, the set of k-dimensional exposed faces of P is finite and represented by a Finset of cardinality faceCount P k; moreover, if a stellar subdivision P' decomposes the j-faces into old j-faces (minus F0 at j = d - 1) and a disjoint family of new j-faces in bijection with j-element subsets of Fin d, then faceCount P' j = faceCount P j + d.choose j for j + 1 < d and faceCount P' (d - 1) = faceCount P (d - 1) + (d - 1).
-- source:
--   Grünbaum, Convex Polytopes (2003), Ch. 10

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

set_option autoImplicit false
open scoped Classical

namespace Grunbaum2003

theorem polytope_kFaces_finite_and_stellar_subdivision_card (d : ℕ) (hd : 1 ≤ d) :
    (∀ {P : Set (Fin d → ℝ)}, IsDPolytope P → ∀ (k : ℕ),
      ∃ (ℱ : Finset (Set (Fin d → ℝ))),
        (ℱ : Set (Set (Fin d → ℝ))) =
          {F : Set (Fin d → ℝ) | F.Nonempty ∧ IsExposed ℝ P F ∧
            Module.finrank ℝ (affineSpan ℝ F).direction = k} ∧
        ℱ.card = faceCount P k) ∧
    (∀ {P P' : Set (Fin d → ℝ)}
      (ℱ ℱ' ℱ_new : ℕ → Finset (Set (Fin d → ℝ))),
      (∀ k : ℕ, (ℱ k).card = faceCount P k) →
      (∀ k : ℕ, (ℱ' k).card = faceCount P' k) →
      (∀ j : Fin d, j.val + 1 < d →
        ℱ' j.val = ℱ j.val ∪ ℱ_new j.val ∧
        Disjoint (ℱ j.val) (ℱ_new j.val) ∧
        Nonempty (ℱ_new j.val ≃ (Finset.univ : Finset (Fin d)).powersetCard j.val)) →
      ∀ (F₀ : Set (Fin d → ℝ)), F₀ ∈ ℱ (d - 1) →
      (ℱ' (d - 1) = (ℱ (d - 1)).erase F₀ ∪ ℱ_new (d - 1) ∧
        Disjoint ((ℱ (d - 1)).erase F₀) (ℱ_new (d - 1)) ∧
        Nonempty (ℱ_new (d - 1) ≃ (Finset.univ : Finset (Fin d)).powersetCard (d - 1))) →
      (∀ j : Fin d, j.val + 1 < d → faceCount P' j.val = faceCount P j.val + Nat.choose d j.val) ∧
      faceCount P' (d - 1) = faceCount P (d - 1) + (d - 1)) := by sorry

end Grunbaum2003
