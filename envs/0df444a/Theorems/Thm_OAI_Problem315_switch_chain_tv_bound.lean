-- Prove2me | Theorems.Thm_OAI_Problem315_switch_chain_tv_bound
-- name    : OAI.Problem315.switch_chain_tv_bound
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:07.424187+00:00
-- url     : https://prove2.me/theorems/7aba6660-1232-4038-9351-96f6b70a1f9d
-- statement:
--   The theorem states that, for every number of vertices n ≥ 4 and every degree assignment d : Fin n → ℕ with each d(v) ≤ n−1 that is graphical (some simple graph on vertex set Fin n has degree d(v) at every vertex v), if the set of such realizing graphs has more than one element (stateCount n d > 1), then for every number of steps t ≥ 0 and every starting realization G, the total variation distance after t steps from G to the uniform distribution on realizations is at most (√N / 2) · exp(−t / (24 n² · C(n,4))), where N is the number of realizing graphs and C(n,4) is the binomial coefficient. Here the chain is the lazy switch chain: from a graph it stays put with probability 1/2, and otherwise each of the 12·C(n,4) proposals, consisting of a 4-element vertex set and an ordered pair of distinct perfect matchings on it, is applied when the first matching consists of edges of the current graph and the second consists of non-edges, replacing the first by the second, and otherwise leaves the graph unchanged, each proposal carrying weight 1/(12·C(n,4)). The distance tvDistanceFrom n d t G is half the sum over realizations H of |P^t(G,H) − 1/N|, where P^t is the t-step transition kernel. The statement is admitted in the source without proof.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SwitchChain.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SwitchChain.lean; bytes 5128..5465
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_SwitchChain

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem315

theorem switch_chain_tv_bound :
    ∀ (n : Nat) (d : Fin n → Nat), 4 ≤ n → (∀ v, d v ≤ n - 1) → Graphical n d → 1 < stateCount n d → ∀ (t : Nat) (G : GraphState n d), tvDistanceFrom n d t G ≤ Real.sqrt (stateCount n d : ℝ) / 2 * Real.exp (- (t : ℝ) / (24 * (n : ℝ) ^ 2 * (Nat.choose n 4 : ℝ))) := by
  sorry

end Problem315
end
end OAI
