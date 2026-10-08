-- Prove2me | Theorems.Thm_OAI_EuclideanRamsey_TransitiveConsequence_subset_of_finite_transitive_ramsey
-- name    : OAI.EuclideanRamsey.TransitiveConsequence.subset_of_finite_transitive_ramsey
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:38.516977+00:00
-- url     : https://prove2.me/theorems/5b562835-0147-496b-bc23-905e990e07c3
-- statement:
--   The theorem states that, for natural numbers s, t and D, a family a of s points in D-dimensional Euclidean space (indexed by Fin s) and a family y of t points in the same space (indexed by Fin t), with s > 0, a injective, and y injective, the following holds. Suppose y is transitive in the sense that for any indices i and j there is a permutation σ of Fin t that preserves all pairwise distances, dist(y(σk), y(σl)) = dist(y k, y l) for all k and l, and sends i to j. Suppose also that the set of points of a is contained in the set of points of y. Then a is Ramsey. Here Ramsey means that for every number of colours r ≥ 2 there exists a dimension D' ≥ 1 such that for every colouring c of D'-dimensional Euclidean space with r colours, there is a congruent copy b of a, meaning dist(b i, b j) = dist(a i, a j) for all i and j, whose points all receive the same colour. The theorem is stated with its proof admitted.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/EuclideanRamseyTransitive.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/EuclideanRamseyTransitive.lean; bytes 505..898
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_EuclideanRamseyTransitive

namespace OAI

namespace EuclideanRamsey

namespace TransitiveConsequence

theorem subset_of_finite_transitive_ramsey {s t D : ℕ}
    (a : Fin s → Space D) (y : Fin t → Space D)
    (hs : 0 < s) (ha : Function.Injective a) (_hy : Function.Injective y)
    (htrans : ∀ i j : Fin t, ∃ σ : Equiv.Perm (Fin t),
      (∀ k l : Fin t, dist (y (σ k)) (y (σ l)) = dist (y k) (y l)) ∧ σ i = j)
    (hsub : Set.range a ⊆ Set.range y) : Ramsey a := by
  sorry

end TransitiveConsequence
end EuclideanRamsey
end OAI
