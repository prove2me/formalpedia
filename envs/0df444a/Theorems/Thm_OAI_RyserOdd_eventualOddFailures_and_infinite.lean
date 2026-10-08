-- Prove2me | Theorems.Thm_OAI_RyserOdd_eventualOddFailures_and_infinite
-- name    : OAI.RyserOdd.eventualOddFailures_and_infinite
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:17.670878+00:00
-- url     : https://prove2.me/theorems/57adf8fb-fcd9-45e0-85e6-d0cbdfa3bdaf
-- statement:
--   The theorem states that two things hold. First, there is a threshold N such that for every prime p ≥ N with p ≡ 2 (mod 3), there is a degree threshold D ≥ 3 such that for every odd d ≥ D, ExplicitFailureAt(p^d + 1) holds. Second, the set of ranks r for which ExplicitFailureAt(r) holds is infinite. Here ExplicitFailureAt(r) means that r > 0 and there exist a finite type of vertices with decidable equality and a nonempty hypergraph (a finset of finsets of vertices) on it that is r-partite (some map from vertices to Fin r makes each edge contain exactly one vertex from every part), r-uniform (every edge has exactly r vertices), and intersecting (any two distinct edges share a vertex), and that has at least one vertex cover (a vertex set meeting every edge). Moreover its matching number, the largest size of a family of pairwise disjoint edges, equals 1, and its cover number, the least size of a vertex cover, equals r. Consequently (r − 1)·(matching number) < cover number, so the hypergraph violates the Ryser-type bound cover number ≤ (r − 1)·matching number.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/RyserOddExtensions.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/RyserOddExtensions.lean; bytes 2386..2827
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_RyserOddExtensions

namespace OAI

noncomputable section

namespace RyserOdd

open RyserCoveringCounterexample

theorem eventualOddFailures_and_infinite :
    (∃ primeThreshold : ℕ, ∀ prime : ℕ, primeThreshold ≤ prime →
      prime.Prime → prime % 3 = 2 →
      ∃ degreeThreshold : ℕ, 3 ≤ degreeThreshold ∧
        ∀ degree : ℕ, degreeThreshold ≤ degree → Odd degree →
          Specification.ExplicitFailureAt (prime ^ degree + 1)) ∧
    Set.Infinite {rank : ℕ | Specification.ExplicitFailureAt rank} := by
  sorry

end RyserOdd
end
end OAI
