-- Prove2me | Theorems.Thm_OAI_SimpleAmenable_main
-- name    : OAI.SimpleAmenable.main
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:22.006528+00:00
-- url     : https://prove2.me/theorems/0548f53c-54eb-4d98-86f6-a00778d480bc
-- statement:
--   The theorem states that there exists a group G, with underlying type in the lowest universe, that is infinite, finitely presented, simple, and Følner-amenable. Here FolnerAmenable(G) is the defined proposition that for every finite subset K of G and every real ε>0 there is a nonempty finite subset D of G such that, for every g in K, the symmetric difference between the left translate gD={g·d : d∈D} and D has cardinality strictly less than ε times the cardinality of D. Simple means G is nontrivial and has no normal subgroups other than the trivial one and G itself, and finitely presented means G has a presentation with finitely many generators and finitely many relations. The statement is admitted without proof in the source.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SimpleAmenable.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SimpleAmenable.lean; bytes 329..475
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_SimpleAmenable

namespace OAI

open scoped symmDiff

namespace SimpleAmenable

theorem main : ∃ (G : Type) (_ : Group G),
    Infinite G ∧ Group.IsFinitelyPresented G ∧ IsSimpleGroup G ∧ FolnerAmenable G := by
  sorry

end SimpleAmenable
end OAI
