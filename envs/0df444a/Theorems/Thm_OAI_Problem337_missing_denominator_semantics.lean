-- Prove2me | Theorems.Thm_OAI_Problem337_missing_denominator_semantics
-- name    : OAI.Problem337.missing_denominator_semantics
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:09.646008+00:00
-- url     : https://prove2.me/theorems/f1bc1eb9-abcf-47b3-b5e3-6680a6736cea
-- statement:
--   The theorem states that, for every natural number k, writing a k-term one-expansion as a strictly increasing list of k positive integer denominators n₀<…<n_{k-1} (each at least 1) whose reciprocals sum exactly to 1, and letting D(k) be the set of integers m ≥ 2 that occur as a denominator in at least one such expansion, the following all hold. D(k) is a finite set, and the set of missing denominators, meaning integers m ≥ 2 not in D(k), is nonempty. Let v(k) be the least missing denominator. Then v(k) ≥ 2 and v(k) is not in D(k), every integer m with 2 ≤ m < v(k) does lie in D(k), and, when k ≥ 1, v(k) ≤ 1 + k^(2^(k-1)). The statement is admitted with sorry, not proved here.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/EgyptianFractions.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/EgyptianFractions.lean; bytes 2967..3242
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_EgyptianFractions

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem337

theorem missing_denominator_semantics :
    ∀ k : ℕ,
  Set.Finite (D k) ∧
  (∃ m : ℕ, m ∈ missingDenominators k) ∧
  2 ≤ v k ∧ v k ∉ D k ∧
  (∀ m : ℕ, 2 ≤ m → m < v k → m ∈ D k) ∧
  (1 ≤ k → v k ≤ 1 + k ^ (2 ^ (k - 1))) := by
  sorry

end Problem337
end
end OAI
