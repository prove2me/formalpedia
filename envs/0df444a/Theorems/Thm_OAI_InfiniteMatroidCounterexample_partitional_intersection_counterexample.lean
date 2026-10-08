-- Prove2me | Theorems.Thm_OAI_InfiniteMatroidCounterexample_partitional_intersection_counterexample
-- name    : OAI.InfiniteMatroidCounterexample.partitional_intersection_counterexample
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:46.63159+00:00
-- url     : https://prove2.me/theorems/2069702c-86c5-48b1-a57d-01734dbfc7db
-- statement:
--   The theorem states that the ground set E = ℤ × D is countably infinite, where D is the set of pairs (m, f) with m a natural number and f a Boolean function on Boolean m-tuples, and that there is a matroid Q on E0 = D × Bool with ground set all of E0, equal to its own dual, and uniform in the sense that every subset of the ground set is independent or spanning, such that the following hold for the two matroids M₀ = rayMatroid(Q, false) and M₁ = rayMatroid(Q, true) on E. Each rayMatroid(Q, p) is the direct sum of copies of Q, one for each integer of parity p (even for false, odd for true), transported to ground set ℤ × D by an explicit bijection that sends the element (x, b) of the copy at integer n to (bundleAt(n, b), x). Both M₀ and M₁ have ground set all of E and are self-dual. Each is partitional, meaning it is, up to a bijection of ground sets, a direct sum (sigma sum) of uniform matroids over some index type. For every independent set I₀ of M₀ and independent set I₁ of M₁, the union I₀ ∪ I₁ is not all of E. Finally, the pair (M₀, M₁) fails the packing-covering property, which would require a split of E into P and C, disjoint subsets S₀, S₁ of P spanning in the restrictions M₀|P and M₁|P respectively, and subsets I₀, I₁ covering C that are independent in the contractions of M₀ and M₁ onto C, and it also fails the intersection property, which would require a common independent set J of both matroids split into disjoint J₀, J₁ with closure_{M₀}(J₀) ∪ closure_{M₁}(J₁) = E.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/InfiniteMatroidCorollaries.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/InfiniteMatroidCorollaries.lean; bytes 4634..5180
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_InfiniteMatroidCorollaries

namespace OAI

namespace InfiniteMatroidCounterexample

open Set Matroid

theorem partitional_intersection_counterexample :
    Countable E ∧ Infinite E ∧
    ∃ Q : Matroid E0, Q.E = univ ∧ Q.dual = Q ∧ IsUniform Q ∧
      let M₀ := rayMatroid Q false
      let M₁ := rayMatroid Q true
      M₀.E = univ ∧ M₁.E = univ ∧ M₀.dual = M₀ ∧ M₁.dual = M₁ ∧
      IsPartitional M₀ ∧ IsPartitional M₁ ∧
      (∀ I₀ I₁ : Set E, M₀.Indep I₀ → M₁.Indep I₁ → I₀ ∪ I₁ ≠ univ) ∧
      ¬ HasPackingCovering M₀ M₁ ∧ ¬ HasIntersection M₀ M₁ := by
  sorry

end InfiniteMatroidCounterexample
end OAI
