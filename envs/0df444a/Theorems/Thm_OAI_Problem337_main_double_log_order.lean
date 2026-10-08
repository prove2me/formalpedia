-- Prove2me | Theorems.Thm_OAI_Problem337_main_double_log_order
-- name    : OAI.Problem337.main_double_log_order
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:09.517599+00:00
-- url     : https://prove2.me/theorems/034e7e57-4f39-4123-a938-b552579bba78
-- statement:
--   The theorem states that there exist real constants c₁>0 and c₂>0 and a natural number b₀ such that, for every natural number b ≥ b₀, c₁·log(log b) ≤ L(b) ≤ c₂·log(log b), where L(b)=maxEgyptianLength(b) is cast to a real number. Here L(b) is the maximum, over integers a with 1 ≤ a < b, of the egyptianLength of a/b, which is the least k for which a/b can be written as a sum of k unit fractions 1/n₀+…+1/n_{k−1} with every denominator at least 2 and the denominators strictly increasing (so distinct). The theorem therefore asserts that the worst-case minimal number of terms in an Egyptian fraction representation of a proper fraction with denominator b is of order log log b, with both a lower and an upper bound holding for all sufficiently large b.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/EgyptianFractions.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/EgyptianFractions.lean; bytes 1523..1799
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_EgyptianFractions

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem337

theorem main_double_log_order :
    ∃ c1 c2 : ℝ, 0 < c1 ∧ 0 < c2 ∧ ∃ b0 : ℕ,
  ∀ b : ℕ, b0 ≤ b →
    c1 * Real.log (Real.log (b : ℝ)) ≤ (maxEgyptianLength b : ℝ) ∧
    (maxEgyptianLength b : ℝ) ≤ c2 * Real.log (Real.log (b : ℝ)) := by
  sorry

end Problem337
end
end OAI
