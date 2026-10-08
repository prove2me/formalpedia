-- Prove2me | Theorems.Thm_OAI_ThreeState_TreeClauses_Tree_poisson_reconstructs_above_KS
-- name    : OAI.ThreeState.TreeClauses.Tree.poisson_reconstructs_above_KS
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:31.408391+00:00
-- url     : https://prove2.me/theorems/66d897ab-bf74-4aec-8129-5b2ab24fd742
-- statement:
--   The theorem states that, for any nonnegative real d and any real lam in the admissible range -1/2 ≤ lam ≤ 1, if the Kesten–Stigum-type inequality 1 < d·lam² holds, then the Poisson(d) offspring distribution reconstructs. Here the model is a Galton–Watson tree whose root has a spin uniformly distributed on three states, and each child's spin is obtained through a channel that keeps the parent's spin with probability (1+2lam)/3 and moves to each other spin with probability (1−lam)/3. The number of children of each vertex is drawn from the offspring law, which here is the Poisson distribution with mean d, with weights e^{-d} d^k / k!. At depth ℓ, the observation is the nested multiset of the spins of descendants, with the leaves at depth ℓ recorded as spins. The posterior of the root spin given an observation is computed from the uniform prior and the observation law, and the advantage at depth ℓ is the expected total variation distance (half the sum of absolute deviations) between this posterior and the uniform distribution on three spins. Reconstructs means that the advantage converges, as ℓ tends to infinity, to some strictly positive limit a.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/ThreeStateTreeClauses.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/ThreeStateTreeClauses.lean; bytes 3576..3746
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_ThreeStateTreeClauses

namespace OAI

noncomputable section

open scoped BigOperators ENNReal NNReal

open Filter

open scoped Topology

namespace ThreeState.TreeClauses.Tree

theorem poisson_reconstructs_above_KS (d : ℝ≥0) (lam : ℝ) (hlam : Admissible lam)
    (hKS : 1 < (d:ℝ)*lam^2) : Reconstructs lam hlam (poissonPMF d) := by
  sorry

end ThreeState.TreeClauses.Tree
end
end OAI
