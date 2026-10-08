-- Prove2me | Theorems.Thm_OAI_Problem315_switch_chain_main
-- name    : OAI.Problem315.switch_chain_main
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:07.287864+00:00
-- url     : https://prove2.me/theorems/e5ccb7aa-18d5-4d5f-b423-5971cccf2e46
-- statement:
--   The theorem states that for every n ≥ 4 and every degree sequence d : Fin n → ℕ with each d(v) ≤ n−1 that is graphical (some simple graph on vertex set Fin n has degree d(v) at every vertex v), the following three things hold for the switch Markov chain on the set of such realizing graphs. The chain, at each step, stays put with probability 1/2 plus the probability of proposals that leave the graph unchanged; otherwise it picks a 4-element vertex set S and an ordered pair of distinct perfect matchings on S, each such proposal having weight 1/(12·C(n,4)), and it replaces the first matching's edges by the second's when all edges of the first are present and none of the second are present, and otherwise stays. (1) The mixing time exists and is at most 2n^8, where it is the least t such that, from every starting graph, the total variation distance between the t-step distribution and the uniform distribution on realizations is at most 1/4. (2) If there is exactly one realizing graph, the chain is already mixed at time 0 and the mixing time is 0. (3) If there is more than one realizing graph, the chain has spectral gap at least 1/(24·n^2·C(n,4)): for every real function f on realizations, this constant times the variance of f under the uniform measure is at most the Dirichlet energy, the uniform average of f·(f − Pf), where P is the chain's transition operator.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SwitchChain.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SwitchChain.lean; bytes 4693..5126
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_SwitchChain

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem315

theorem switch_chain_main :
    ∀ (n : Nat) (d : Fin n → Nat), 4 ≤ n → (∀ v, d v ≤ n - 1) → Graphical n d → ((∃ h : (∃ t : Nat, MixedAt n d t), mixingTime n d h ≤ 2 * n ^ 8) ∧ (stateCount n d = 1 → (MixedAt n d 0 ∧ ∀ h : (∃ t : Nat, MixedAt n d t), mixingTime n d h = 0)) ∧ (1 < stateCount n d → hasSpectralGapAtLeast n d ((1 : ℝ) / (24 * (n : ℝ) ^ 2 * (Nat.choose n 4 : ℝ))))) := by
  sorry

end Problem315
end
end OAI
