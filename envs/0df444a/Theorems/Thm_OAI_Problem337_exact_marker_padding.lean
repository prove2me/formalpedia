-- Prove2me | Theorems.Thm_OAI_Problem337_exact_marker_padding
-- name    : OAI.Problem337.exact_marker_padding
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:09.384531+00:00
-- url     : https://prove2.me/theorems/43e4a3f6-9642-40bc-8fab-9df1904eaa41
-- statement:
--   The theorem states that, for every integer r ≥ 3 and every strictly increasing sequence n₀ < n₁ < ... < n_{r−1} of r positive integers whose reciprocals sum exactly to 1 (a one-expansion, where the entries need only be at least 1), and for every natural number m that occurs as one of the entries n_i, there is a strictly increasing sequence of r+1 positive integers whose reciprocals also sum exactly to 1 and which still contains m as one of its entries. In other words, any one-expansion of length r ≥ 3 containing a given value m can be replaced by a one-expansion of length r+1 that also contains m. The theorem is admitted in the source and is not proved there.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/EgyptianFractions.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/EgyptianFractions.lean; bytes 2292..2545
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_EgyptianFractions

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem337

theorem exact_marker_padding :
    ∀ r : ℕ, 3 ≤ r → ∀ n : Fin r → ℕ, IsOneExpansion n →
  ∀ m : ℕ, (∃ i : Fin r, n i = m) →
    ∃ n' : Fin (r + 1) → ℕ,
      IsOneExpansion n' ∧ ∃ i : Fin (r + 1), n' i = m := by
  sorry

end Problem337
end
end OAI
