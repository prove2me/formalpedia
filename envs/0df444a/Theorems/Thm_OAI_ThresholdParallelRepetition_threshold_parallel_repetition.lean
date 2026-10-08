-- Prove2me | Theorems.Thm_OAI_ThresholdParallelRepetition_threshold_parallel_repetition
-- name    : OAI.ThresholdParallelRepetition.threshold_parallel_repetition
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:32.195098+00:00
-- url     : https://prove2.me/theorems/5efabb38-b423-4ef5-b80f-a89f9f277cfa
-- statement:
--   The theorem states that there is a universal constant κ₀>0 such that the following holds for every two-player nonlocal game G with question sets of sizes x+1 and y+1 and answer sets of sizes a+1 and b+1, given by a probability distribution on question pairs and a Boolean acceptance predicate on questions and answers, whose entangled value is strictly less than 1. Here the entangled value is the supremum of the winning probability over finite-dimensional entangled strategies, which consist of a unit state on a bipartite space, positive semidefinite measurement operators for Alice and Bob summing to the identity for each question, with answer probabilities given by the Born rule. For every δ with 0<δ<1−entangledValue(G) and every number of repetitions k≥1, consider k-fold parallel repetition, where k independent question pairs are drawn from G's distribution and the players answer all coordinates at once. The threshold probability of a repeated entangled strategy S is the probability that the number of coordinates won is at least ⌈(entangledValue(G)+δ)k⌉. The theorem asserts that this probability is at most exp(−κ₀ δ¹³ k /(1+ln((a+1)(b+1)))) for every repeated strategy S, and that the threshold value, defined as the supremum of the threshold probability over all repeated strategies, satisfies the same bound. The statement is admitted without proof in the source.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/EntangledGames.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/EntangledGames.lean; bytes 2556..3132
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_EntangledGames

namespace OAI

noncomputable section

open scoped BigOperators ComplexOrder

namespace ThresholdParallelRepetition

theorem threshold_parallel_repetition :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧
      ∀ (x y a b : ℕ) (G : Game x y a b), entangledValue G < 1 →
      ∀ (δ : ℝ), 0 < δ → δ < 1 - entangledValue G →
      ∀ (k : ℕ), 1 ≤ k →
        (∀ S : RepeatedStrategy x y a b k,
          thresholdProbability G δ S ≤
            Real.exp (-κ₀ * δ ^ 13 / (1 + Real.log (((a + 1) * (b + 1) : ℕ) : ℝ)) * k)) ∧
        thresholdValue (k := k) G δ ≤
          Real.exp (-κ₀ * δ ^ 13 / (1 + Real.log (((a + 1) * (b + 1) : ℕ) : ℝ)) * k) := by
  sorry

end ThresholdParallelRepetition
end
end OAI
