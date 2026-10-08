-- Prove2me | Theorems.Thm_OAI_PartitionConsistency_main_consistency
-- name    : OAI.PartitionConsistency.main_consistency
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:01.044345+00:00
-- url     : https://prove2.me/theorems/877b5995-ce1b-4fe3-b6c5-d095d53e47f5
-- statement:
--   The theorem states a relative consistency result in pure first-order set theory with membership and equality: if ZF, meaning the full axioms of extensionality, empty set, pairing, union, power set, infinity and foundation together with every instance of Separation and Replacement for arbitrary formulas with arbitrary parameters, and without Choice, is consistent, then so is the theory obtained by adding three sentences to ZF. Consistency is syntactic: no finite classical natural-deduction derivation of falsity exists from the theory, allowing any finite supply of free variables. The added sentences are the Partition Principle PP, which says that whenever there is a set surjection from X onto Y then there is a set injection from Y into X, with functions coded internally as sets of Kuratowski pairs and the injection not required to be a section of the surjection; the ordinal-indexed Choice axiom ACwo, which says that for every internal von Neumann ordinal (transitive and internally well-ordered by membership) every family of nonempty sets indexed by it has a choice function; and the negation of full Axiom of Choice AC, which says that every set of nonempty sets has a choice function.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PartitionConsistency.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/PartitionConsistency.lean; bytes 14606..14826
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_PartitionConsistency

namespace OAI

namespace PartitionConsistency

/-- Relative consistency of ZF with the Partition Principle, ordinal-indexed
Choice and failure of Choice. -/
theorem main_consistency :
    Consistent SetLanguage.ZF → Consistent SetLanguage.targetTheory := by
  sorry

end PartitionConsistency
end OAI
