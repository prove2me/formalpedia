-- Prove2me | Theorems.Thm_OAI_Problem337_every_exact_marker_occurs
-- name    : OAI.Problem337.every_exact_marker_occurs
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:09.232397+00:00
-- url     : https://prove2.me/theorems/05a36d43-649d-4e15-8a28-e345dc8626df
-- statement:
--   The theorem states that every integer m ≥ 2 is an exact marker for some length k, in the following sense. Here a one-expansion of length k is a strictly increasing function n from the k indices Fin k to the positive integers such that the sum of the unit fractions 1/n(i) over all i equals 1, and D(k) is the set of integers m ≥ 2 such that some one-expansion of length k has m as one of its terms. The claim is that for every natural number m with 2 ≤ m there exists a natural number k with m ∈ D(k), that is, m appears as a denominator in some strictly increasing length-k decomposition of 1 into distinct unit fractions.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/EgyptianFractions.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/EgyptianFractions.lean; bytes 2547..2648
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_EgyptianFractions

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem337

theorem every_exact_marker_occurs :
    ∀ m : ℕ, 2 ≤ m → ∃ k : ℕ, m ∈ D k := by
  sorry

end Problem337
end
end OAI
