-- Prove2me | Theorems.Thm_OAI_MetricKMedian_main_finite_work
-- name    : OAI.MetricKMedian.main_finite_work
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:56.962055+00:00
-- url     : https://prove2.me/theorems/ffb8207c-ff6e-45fe-bc2f-842096270a37
-- statement:
--   The theorem states that, for every real ε>0, there exist a function algorithm from metric k-median instances to Boolean lists and a proof P that algorithm is computable in polynomial time by a multi-tape Turing machine (Turing.TM2ComputableInPolyTime), with input encoding encodeInstance and identity output encoding, such that every tape alphabet Γ k of the machine is finite and, for every instance I, algorithm(I) is a correct output with parameter ε. An instance consists of n points indexed by Fin n, a rational distance function on them that is nonnegative, zero exactly on equal points, symmetric and satisfies the triangle inequality, a set of clients, a set of facilities, and a number k with 1 ≤ k ≤ the number of facilities. The encoding is a bit-list: n and k in a self-delimiting unary-length binary code, then the indicator bits of the client set and facility set, then every distance entry as a sign bit, numerator magnitude and denominator. For a set S of facilities, the cost is the sum over clients j of the real-valued distance from j to the nearest point of S, and the optimum is the minimum cost over nonempty subsets of the facilities with at most k elements. An output is Correct for ε on I when it is exactly the indicator bit-list over Fin n of some nonempty set S contained in the facilities with |S| ≤ k and cost(S) ≤ (1 + 2/e + ε) times the optimum.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/MetricKMedian.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/MetricKMedian.lean; bytes 1912..2169
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_MetricKMedian

namespace OAI

section

section

namespace MetricKMedian

theorem main_finite_work : ∀ ε : ℝ, 0 < ε →
    ∃ (algorithm : Instance → List Bool) (P : Turing.TM2ComputableInPolyTime encodeInstance id algorithm),
      (∀ k : P.tm.K, Finite (P.tm.Γ k)) ∧ ∀ I, Correct ε I (algorithm I) := by
  sorry

end MetricKMedian
end
end
end OAI
