-- Prove2me | Theorems.Thm_OAI_Problem344_large_gaps_and_ratio_density
-- name    : OAI.Problem344.large_gaps_and_ratio_density
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:10.357144+00:00
-- url     : https://prove2.me/theorems/7da1c158-83a6-4180-b34e-dfb84257c3ea
-- statement:
--   The theorem states a conjunction of two claims about primes, with p_n denoting the nth prime (p_1=2, p_2=3, and so on). First, for every real C>0 there exist a real c>0 and a natural number N₀ such that for all N≥N₀, the number of indices n in {1,…,N} with a large gap after p_n, meaning C·log p_n < p_{n+1} − p_n, is at least c·N. Second, the lower asymptotic density of the set of indices n≥1 with p_n/n < p_{n+1}/(n+1) is strictly positive. Here the lower asymptotic density of a set A of naturals is defined as the supremum of all reals d for which there is an N₀ such that, for every N≥N₀, d ≤ (the number of elements of A in {1,…,N})/N. This theorem is admitted in the source without a proof.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PrimeGaps.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/PrimeGaps.lean; bytes 884..1170
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_PrimeGaps

namespace OAI

noncomputable section

namespace Problem344

theorem large_gaps_and_ratio_density :
    (∀ C : ℝ, 0 < C →
      ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        c * (N : ℝ) ≤ ((LargePrimeGaps.largeGapIndices C N).card : ℝ)) ∧
    0 < lowerAsymptoticDensity ratioIncreaseIndices := by
  sorry

end Problem344
end
end OAI
