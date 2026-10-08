-- Prove2me | Theorems.Thm_OAI_Problem337_egyptian_length_is_minimum
-- name    : OAI.Problem337.egyptian_length_is_minimum
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:09.096622+00:00
-- url     : https://prove2.me/theorems/43b10430-ee80-49bd-8121-32726bfcd71c
-- statement:
--   The theorem states that for all natural numbers a and b with 1 ≤ a < b, the rational a/b has an Egyptian expansion of length egyptianLength(a,b), and no Egyptian expansion is shorter. Here an Egyptian expansion of x of length k is a function n from Fin k to the naturals such that every n(i) ≥ 2, n is strictly increasing (so the denominators are distinct), and the sum over i of 1/n(i) equals x. The set egyptianLengths(a,b) consists of all k for which a/b has such an expansion, and egyptianLength(a,b) is defined as the infimum (sInf) of this set. Concretely, the theorem asserts both that a/b has an expansion of length egyptianLength(a,b), and that any k admitting an expansion of a/b satisfies egyptianLength(a,b) ≤ k, so this length is the minimum number of distinct unit fractions with denominators at least 2 needed to write a/b. The statement is admitted without proof in the source.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/EgyptianFractions.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/EgyptianFractions.lean; bytes 1205..1521
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_EgyptianFractions

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem337

theorem egyptian_length_is_minimum :
    ∀ a b : ℕ, 1 ≤ a → a < b →
  (∃ n : Fin (egyptianLength a b) → ℕ,
    IsEgyptianExpansion ((a : ℚ) / (b : ℚ)) n) ∧
  (∀ k : ℕ, (∃ n : Fin k → ℕ,
    IsEgyptianExpansion ((a : ℚ) / (b : ℚ)) n) →
    egyptianLength a b ≤ k) := by
  sorry

end Problem337
end
end OAI
