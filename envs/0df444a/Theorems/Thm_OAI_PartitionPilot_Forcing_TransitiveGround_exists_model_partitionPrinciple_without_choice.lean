-- Prove2me | Theorems.Thm_OAI_PartitionPilot_Forcing_TransitiveGround_exists_model_partitionPrinciple_without_choice
-- name    : OAI.PartitionPilot.Forcing.TransitiveGround.exists_model_partitionPrinciple_without_choice
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:01.269357+00:00
-- url     : https://prove2.me/theorems/1342629b-44d7-466a-80fa-72b0838f317a
-- statement:
--   The theorem states that, for a countable transitive collection M of sets (a transitive ground, meaning every element of a member of M lies in M) that satisfies, when quantifiers are relativized to M, the pairing, union, power set and infinity axioms, the separation and collection schemas for formulas in the language of equality and membership with parameters from M, and the axiom of choice, and for a set K in M that is a standard inaccessible relative to M, there exists a transitive collection N of sets with M ⊆ N such that N satisfies the finite list of axioms (extensionality, foundation, empty set, pairing, union, power set, infinity) together with the separation and replacement schemas, N satisfies the partition principle, and N does not satisfy the axiom of choice. Here the partition principle says that for all sets a, b and f, if f is a function from a onto b then there is an injection from b into a. K being a standard inaccessible relative to M means: K is a transitive set of transitive sets such that no β in K admits an injection from K into β lying in M; no injection from K into ω lies in M; no function in M maps some α in K into K with values bounding every element of K (an element equal to or below some value); and for every M-cardinal κ in K, the M-subsets of κ (the subsets of κ that belong to M) inject, via a function in M, into some element of K.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PartitionPrinciple.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/PartitionPrinciple.lean; bytes 9348..10073
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_PartitionPrinciple

namespace OAI

namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula

universe u

variable (M : TransitiveGround.{u})

theorem exists_model_partitionPrinciple_without_choice
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (small : M.sets.Countable)
    {K : ZFSet.{u}} (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K) :
    ∃ N : TransitiveGround.{u}, M.sets ⊆ N.sets ∧ ZFRealization N.sets ∧
      Realize N.sets partitionPrinciple Fin.elim0 ∧
      ¬ Realize N.sets SetFormula.choice Fin.elim0 := by
  sorry

end PartitionPilot.Forcing.TransitiveGround
end OAI
