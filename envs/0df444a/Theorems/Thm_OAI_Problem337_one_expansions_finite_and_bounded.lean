-- Prove2me | Theorems.Thm_OAI_Problem337_one_expansions_finite_and_bounded
-- name    : OAI.Problem337.one_expansions_finite_and_bounded
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:09.768509+00:00
-- url     : https://prove2.me/theorems/50f763e7-dee4-4ddc-ab67-c02bb4b01161
-- statement:
--   The theorem states two things about expansions of 1 as sums of distinct unit fractions with a fixed number of terms. A one-expansion of length k is a strictly increasing function n from {0,…,k−1} to the natural numbers with every n(i) ≥ 1 and 1/n(0) + … + 1/n(k−1) = 1; OneExpansions(k) is the set of all such n, and F(k) is its cardinality as given by Set.ncard. First, for every natural number k, the set OneExpansions(k) is finite and F(k) ≤ k^(2^k − 1). Second, for every k and every one-expansion n of length k, each term obeys the bound n(i) ≤ k^(2^i) for every index i < k, counting indices from zero. The statement is admitted without proof in the source.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/EgyptianFractions.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/EgyptianFractions.lean; bytes 1801..2046
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_EgyptianFractions

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem337

theorem one_expansions_finite_and_bounded :
    (∀ k : ℕ, Set.Finite (OneExpansions k) ∧
    F k ≤ k ^ (2 ^ k - 1)) ∧
  (∀ k : ℕ, ∀ n : Fin k → ℕ, IsOneExpansion n →
    ∀ i : Fin k, n i ≤ k ^ (2 ^ i.val)) := by
  sorry

end Problem337
end
end OAI
