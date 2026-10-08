-- Prove2me | Theorems.Thm_OAI_EuclideanRamsey_classification
-- name    : OAI.EuclideanRamsey.classification
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:38.668977+00:00
-- url     : https://prove2.me/theorems/980a2e1e-ef52-4c6e-9c96-9087ddeea5f4
-- statement:
--   The theorem states that, for natural numbers s ≥ 2 and d ≥ 1 and an injective configuration a of s points in d-dimensional Euclidean space whose affine span over ℝ is all of ℝ^d, the configuration is Ramsey if and only if it satisfies the field criterion. Ramsey means that for every number of colours r ≥ 2 there is a dimension D ≥ 1 such that every colouring c of ℝ^D with r colours admits a monochromatic congruent copy of a, that is, points b₀,...,b_{s-1} in ℝ^D with |bᵢ−bⱼ| = |aᵢ−aⱼ| for all i, j, all given the same colour. The field criterion is formulated over the field K generated over ℚ by all coordinates of the points aᵢ, inside ℝ. It asks for a matrix P, indexed by {none, 1,...,d} (the augmented index set), with entries in the tensor product K ⊗_ℚ K, such that two conditions hold. First, for every point i, using the augmented vector (1, aᵢ₁,...,aᵢd), the sum over α, β of (augmented(i,α) ⊗ 1) · P(α,β) · (1 ⊗ augmented(i,β)) equals 0. Second, applying the multiplication map K ⊗_ℚ K → K to each entry P(α,β) with α and β both coordinate indices gives 1 when α = β and 0 otherwise.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/EuclideanRamsey.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/EuclideanRamsey.lean; bytes 1662..1881
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_EuclideanRamsey

namespace OAI

noncomputable section

open scoped TensorProduct

namespace EuclideanRamsey

theorem classification {s d : ℕ} (a : Fin s → Space d)
    (hs : 2 ≤ s) (hd : 1 ≤ d) (ha : Function.Injective a)
    (hspan : affineSpan ℝ (Set.range a) = ⊤) :
    Ramsey a ↔ FieldCriterion a := by
  sorry

end EuclideanRamsey
end
end OAI
