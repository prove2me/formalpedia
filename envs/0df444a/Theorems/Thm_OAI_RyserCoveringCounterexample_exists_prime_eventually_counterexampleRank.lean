-- Prove2me | Theorems.Thm_OAI_RyserCoveringCounterexample_exists_prime_eventually_counterexampleRank
-- name    : OAI.RyserCoveringCounterexample.exists_prime_eventually_counterexampleRank
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:17.473367+00:00
-- url     : https://prove2.me/theorems/34053039-84c6-4169-9488-97dcc1a029c2
-- statement:
--   The theorem states that there is a prime p with p > 5 and p ≡ 2 (mod 3), together with a threshold N, such that for every prime n ≥ N with n > 2, the number r = p^n + 1 satisfies CounterexampleRank(r). CounterexampleRank(r) means that r is positive and there exist a finite type V with decidable equality and a hypergraph H on V, meaning a finite set of finite subsets of V, such that H is nonempty and r-partite uniform, i.e. V can be labelled by Fin r so that every edge contains exactly one vertex of each label. H must also be intersecting, meaning any two distinct edges share a vertex, and must admit a cover, meaning a vertex set meeting every edge. Its matching number must equal 1, where the matching number is the largest size of a subfamily of pairwise disjoint edges, and its cover number must equal r, where the cover number is the least size of a vertex set meeting every edge.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/RyserCovering.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/RyserCovering.lean; bytes 1485..1709
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_RyserCovering

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample

theorem exists_prime_eventually_counterexampleRank :
    ∃ p : ℕ, p.Prime ∧ 5 < p ∧ p % 3 = 2 ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → n.Prime → 2 < n →
        CounterexampleRank (p ^ n + 1) := by
  sorry

end RyserCoveringCounterexample
end
end OAI
