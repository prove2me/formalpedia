-- Prove2me | Theorems.Thm_OAI_Problem337_counting_double_log_order
-- name    : OAI.Problem337.counting_double_log_order
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:08.980996+00:00
-- url     : https://prove2.me/theorems/cc62b393-015e-4613-abff-2ff863881479
-- statement:
--   The theorem states that there exist positive real constants c and C and a natural number k₀ such that for every natural number k ≥ k₀, c·k ≤ log(log F(k)) ≤ C·k, where logs are natural real logarithms and F(k) is the number of one-expansions of length k. A one-expansion of length k is a strictly increasing function n from {0,…,k−1} to the natural numbers with every n(i) ≥ 1 and with the sum of the unit fractions 1/n(i) over all i equal to 1, that is, a representation of 1 as a sum of k distinct unit fractions; here the denominator 1 is permitted, and F(k) is the cardinality of this set (as a set cardinality, which would be zero if the set were infinite). The statement is an admitted theorem whose proof is left as sorry.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/EgyptianFractions.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/EgyptianFractions.lean; bytes 2048..2290
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_EgyptianFractions

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem337

theorem counting_double_log_order :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ k0 : ℕ,
  ∀ k : ℕ, k0 ≤ k →
    c * (k : ℝ) ≤ Real.log (Real.log (F k : ℝ)) ∧
    Real.log (Real.log (F k : ℝ)) ≤ C * (k : ℝ) := by
  sorry

end Problem337
end
end OAI
