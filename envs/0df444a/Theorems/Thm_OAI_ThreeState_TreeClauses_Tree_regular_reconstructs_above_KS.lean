-- Prove2me | Theorems.Thm_OAI_ThreeState_TreeClauses_Tree_regular_reconstructs_above_KS
-- name    : OAI.ThreeState.TreeClauses.Tree.regular_reconstructs_above_KS
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:31.537379+00:00
-- url     : https://prove2.me/theorems/0a0ed6ce-4be2-41cc-a0fe-313f5d6cda93
-- statement:
--   The theorem states that, for any natural number b and real number lam in the admissible range -1/2 ≤ lam ≤ 1, if b·lam² > 1, then the three-state broadcast process on a tree whose offspring law is the point mass at b (every vertex has exactly b children) reconstructs. Here the root spin is uniform on three states {0,1,2}, and each edge passes the spin through a channel that keeps it with probability (1+2·lam)/3 and moves it to each other state with probability (1−lam)/3. The observation at depth ℓ is a nested multiset of the spins at that depth, built recursively from the children's observations, and the advantage at depth ℓ is the expected half-L1 distance between the posterior of the root spin given the observation and the uniform distribution on three states, namely the average over observations of half the sum over states of |posterior − 1/3|. Reconstructs means that there is a real a>0 such that this advantage converges to a as ℓ tends to infinity.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/ThreeStateTreeClauses.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/ThreeStateTreeClauses.lean; bytes 3410..3574
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

theorem regular_reconstructs_above_KS (b : ℕ) (lam : ℝ) (hlam : Admissible lam)
    (hKS : 1 < (b:ℝ)*lam^2) : Reconstructs lam hlam (PMF.pure b) := by
  sorry

end ThreeState.TreeClauses.Tree
end
end OAI
