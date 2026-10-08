-- Prove2me | Theorems.Thm_OAI_RandomKSAT_sharpness
-- name    : OAI.RandomKSAT.sharpness
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:14.520457+00:00
-- url     : https://prove2.me/theorems/525931ab-6241-48f7-b498-acd4a188cf28
-- statement:
--   The theorem states the following for every integer k ≥ 3, in a model where an assignment on u variables is a Boolean vector, a width-s clause picks s distinct variables together with a required Boolean value for each, and is satisfied by an assignment that matches at least one of those values. Clauses are drawn independently and uniformly, and blockKill(u,s,S,g) is the probability that no assignment in a finite set S of assignments satisfies all of the first g random width-s clauses. The lifetime of S for width-s clauses is the sum over m ≥ 0 of the probability that S still has a surviving (nonempty) subset after m successive random clauses, each step keeping only the assignments that satisfy the new clause; it is the expected number of clauses until S is emptied. The conclusion is a conjunction of three claims. First, for every real γ < k/(k−1) and all positive reals D and A, and every N, there exist u ≥ max(N,k) and a nonempty set S of assignments such that the one-clause kill probability of width k−1, blockKill(u,k−1,S,1), is at least A·u^{−(k−1)}, while the width-k lifetime of S strictly exceeds D·blockKill(u,k−1,S,1)^{−γ}. Second, there are sizes u(g) ≥ k and nonempty sets S(g), for each g ≥ 2, such that blockKill(u(g),k−1,S(g),1) − blockKill(u(g),k,S(g),g) is asymptotically equivalent as g tends to infinity to 2^{−k}·g^{−(k−1)}. Third, there is no function e with e(g) = o(g^{−(k−1)}) such that for all u ≥ k, all nonempty S and all g ≥ 2 one has blockKill(u,k−1,S,1) − e(g) ≤ blockKill(u,k,S,g). The source states this as an admitted theorem with no proof supplied.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SATSharpness.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SATSharpness.lean; bytes 1728..2711
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_SATSharpness

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

theorem sharpness (k : ℕ) (hk : 3 ≤ k) :
    (∀ γ D A : ℝ, γ < (k : ℝ) / ((k-1 : ℕ) : ℝ) → 0 < D → 0 < A →
      ∀ N : ℕ, ∃ u : ℕ, N ≤ u ∧ k ≤ u ∧ ∃ S : Finset (Assignment u),
        S.Nonempty ∧ A * (u : ℝ) ^ (-((k-1 : ℕ) : ℝ)) ≤ blockKill u (k-1) S 1 ∧
        D * (blockKill u (k-1) S 1) ^ (-γ) < lifetime u k S) ∧
    (∃ u : ℕ → ℕ, ∃ S : ∀ g, Finset (Assignment (u g)),
      (∀ g, 2 ≤ g → k ≤ u g ∧ (S g).Nonempty) ∧
      Asymptotics.IsEquivalent Filter.atTop
        (fun g => blockKill (u g) (k-1) (S g) 1 - blockKill (u g) k (S g) g)
        (fun g => ((2 : ℝ)^k)⁻¹ * (g : ℝ)^(-((k-1 : ℕ) : ℝ)))) ∧
    (¬ ∃ e : ℕ → ℝ,
      Asymptotics.IsLittleO Filter.atTop e (fun g => (g : ℝ)^(-((k-1 : ℕ) : ℝ))) ∧
      ∀ u, k ≤ u → ∀ S : Finset (Assignment u), S.Nonempty → ∀ g, 2 ≤ g →
        blockKill u (k-1) S 1 - e g ≤ blockKill u k S g) := by
  sorry

end RandomKSAT
end
end OAI
