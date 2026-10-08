-- Prove2me | Theorems.Thm_OAI_Thomason_nerveDetection_allDimensions
-- name    : OAI.Thomason.nerveDetection_allDimensions
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:29.591952+00:00
-- url     : https://prove2.me/theorems/af1a387e-6c9b-4248-b4a9-c4dc28b5f266
-- statement:
--   The theorem states that the Thomason weak equivalences on strict ω-categories are exactly the morphisms detected by the Street nerve, in every dimension. Here a morphism of simplicial sets is a simplicial weak equivalence when its geometric realization (the image under the functor from simplicial sets to topological spaces) is a weak homotopy equivalence. The Thomason weak equivalences of ω-categories are defined as the morphisms sent to simplicial weak equivalences by thomasonRight, which is the Street nerve functor from ω-categories to simplicial sets followed by two applications of the Ex functor. The first conclusion is that this class equals the class of ω-functors whose Street nerve alone is a simplicial weak equivalence, so the two applications of Ex can be dropped. The second conclusion is the same statement for each natural number n for the full subcategory of n-truncated ω-categories: the finite-dimensional Thomason weak equivalences, defined through the corresponding finite thomasonRightFinite n (the Street nerve on n-categories followed by Ex twice), coincide with the morphisms of n-categories whose Street nerve is a simplicial weak equivalence. The statement is proved by sorry in the source.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/ThomasonModelStructures.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/ThomasonModelStructures.lean; bytes 135828..136195
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_ThomasonModelStructures

noncomputable section

universe u v w

attribute [instance] OAI.Thomason.DirectedComplex.group

section

namespace OAI

theorem Thomason.nerveDetection_allDimensions :
    OAI.Thomason.thomasonWeakEquivalences.{u} =
      OAI.Thomason.simplicialWeakEquivalences.inverseImage OAI.Thomason.streetNerveFunctor ∧
    ∀ n : ℕ, OAI.Thomason.thomasonWeakEquivalencesFinite.{u} n =
      OAI.Thomason.simplicialWeakEquivalences.inverseImage (OAI.Thomason.streetNerveFinite n) := by
  sorry

end OAI
end
end
