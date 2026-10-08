-- Prove2me | Theorems.Thm_OAI_FourRow_robust_permanent
-- name    : OAI.FourRow.robust_permanent
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:41.549346+00:00
-- url     : https://prove2.me/theorems/48c42c2d-0304-400d-a822-51ba8ad24af4
-- statement:
--   The theorem is stated as admitted, not proved here. Sites are Fin 4, and a law is a real-valued mass function ν on the 24 permutations of the four sites. It states that there exist a real exponent p₀ with 4/3 < p₀ < 2 and a real ε > 0 such that the following holds for every law ν that is a probability law (all masses nonnegative and summing to 1), has total variation distance from the uniform law less than ε (total variation being half the sum over permutations π of |ν(π) − 1/24|), and has uniform marginals (for every pair of sites i and j, the total mass of permutations with π(i)=j equals 1/4). For every 4-by-4 array f of real numbers with all entries f(i,j) ≥ 0, the permanent expectation Σ_π ν(π) ∏_i f(i, π(i)) is at most the product over the four rows i of the normalized ℓ^{p₀} norm of row i, where the norm of a row g is ((Σ_j g(j)^{p₀})/4)^{1/p₀}, using the uniform counting normalization with division by 4.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/FourRowPermanent.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/FourRowPermanent.lean; bytes 910..1234
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_FourRowPermanent

namespace OAI

noncomputable section

namespace FourRow

open scoped BigOperators

theorem robust_permanent :
  ∃ p₀ : ℝ, 4 / 3 < p₀ ∧ p₀ < 2 ∧
    ∃ ε : ℝ, 0 < ε ∧ ∀ ν : Law,
      IsProbability ν → totalVariation ν < ε → UniformMarginals ν →
      ∀ f : Functions, (∀ i j, 0 ≤ f i j) →
        permanentExpectation ν f ≤ ∏ i, lpNorm p₀ (f i) := by
  sorry

end FourRow
end
end OAI
