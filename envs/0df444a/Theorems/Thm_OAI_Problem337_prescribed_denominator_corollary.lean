-- Prove2me | Theorems.Thm_OAI_Problem337_prescribed_denominator_corollary
-- name    : OAI.Problem337.prescribed_denominator_corollary
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:09.892594+00:00
-- url     : https://prove2.me/theorems/af0c78ef-cce1-4f96-92ee-7733f0f2ba45
-- statement:
--   The theorem states a three-part conclusion about v(k), the least integer m ≥ 2 that is not a denominator in any representation of 1 as a sum of k distinct unit fractions 1/n_0 + ... + 1/n_{k-1} with 1 ≤ n_0 < ... < n_{k-1} (the set of such m is D(k), and v(k) is the infimum of its complement within the integers ≥ 2). First, there is a k0 such that for every k ≥ k0, exp(exp(k/600)) ≤ v(k) and v(k) ≤ 1 + k^(2^(k-1)). Second, writing prescribedSlope(k) = log(log v(k))/k, the liminf of prescribedSlope as k tends to infinity is at least (log 2)/257, the liminf is at most the limsup, and the limsup is at most log 2. Third, for every real c < (log 2)/257 there is a k0 such that for all k ≥ k0, exp(exp(c·k)) ≤ v(k). The statement is admitted in the source rather than proved.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/EgyptianFractions.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/EgyptianFractions.lean; bytes 3244..3832
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_EgyptianFractions

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem337

theorem prescribed_denominator_corollary :
    (∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
    Real.exp (Real.exp ((k : ℝ) / 600)) ≤ (v k : ℝ) ∧
    v k ≤ 1 + k ^ (2 ^ (k - 1))) ∧
  (Real.log 2 / 257 ≤ Filter.liminf prescribedSlope Filter.atTop ∧
    Filter.liminf prescribedSlope Filter.atTop ≤
      Filter.limsup prescribedSlope Filter.atTop ∧
    Filter.limsup prescribedSlope Filter.atTop ≤ Real.log 2) ∧
  (∀ c : ℝ, c < Real.log 2 / 257 → ∃ k0 : ℕ,
    ∀ k : ℕ, k0 ≤ k →
      Real.exp (Real.exp (c * (k : ℝ))) ≤ (v k : ℝ)) := by
  sorry

end Problem337
end
end OAI
