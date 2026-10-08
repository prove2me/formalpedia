-- Prove2me | Theorems.Thm_OAI_MetricKMedian_threshold
-- name    : OAI.MetricKMedian.threshold
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:57.106514+00:00
-- url     : https://prove2.me/theorems/bfc25243-7c1d-46f0-8f1e-e5b294e767b6
-- statement:
--   The theorem states that, assuming P ≠ NP (defined as inequality of the class P of languages of bit strings decided in polynomial time and the class NP of languages with polynomially length-bounded witnesses checked by a polynomial-time verifier, where in both cases the underlying Turing machine must have finite work alphabets), the infimum of the set of deterministic polynomial-time approximation factors for metric k-median is exactly 1 + 2/e, with e = exp(1). A k-median instance consists of n points with a rational metric (nonnegative, zero exactly on equal points, symmetric, satisfying the triangle inequality), a set of clients, a set of candidate facilities, and a number k with 1 ≤ k ≤ the number of facilities. The cost of a nonempty facility set S is the sum over clients of the distance to the nearest member of S, and the optimum is the minimum cost over nonempty subsets of the facilities of size at most k. A real α belongs to the set approximationFactors if some algorithm, computable in finite-alphabet polynomial time from the bit encoding of the instance, outputs for every instance the membership mask of a nonempty subset of facilities of size at most k whose cost is at most α times the optimum. The theorem only asserts the value of this infimum, not that it is attained.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/KMedianThreshold.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/KMedianThreshold.lean; bytes 3631..3828
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_KMedianThreshold

namespace OAI

namespace MetricKMedian

/-- The deterministic approximation threshold is an infimum; its attainment is not asserted. -/
theorem threshold (h : Complexity.PNeNP) :
    sInf approximationFactors=1+2/Real.exp 1 := by
  sorry

end MetricKMedian
end OAI
