-- Prove2me | Theorems.Thm_OAI_SimpleFInftyOvergroups_main
-- name    : OAI.SimpleFInftyOvergroups.main
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:22.203935+00:00
-- url     : https://prove2.me/theorems/1971a452-eeaf-4bd5-bea8-c03f41a017c2
-- statement:
--   For a group G, a word in generators g₀,…,g_{n-1} is a list of pairs (i,b), each standing for g_i if b is true and for g_i⁻¹ if false, and evalWord multiplies these letters in order. HasDecidableWordProblem(G) is the proposition that there exist n and elements g₀,…,g_{n-1} of G generating G (the closure of their range is the whole group) such that the set of words evaluating to the identity is a computable predicate. HasTypeFInfty(H) is the proposition that there is a Hausdorff, connected topological space X carrying a CW complex structure on all of X of finite type, with a basepoint x such that H is isomorphic as a group to the fundamental group of X at x, and a surjective covering map p from some space E onto X with E contractible. The theorem states that for every finitely generated group G, in a universe u, that has decidable word problem in this sense, there exist a group H in the same universe that is nontrivial and simple and has type F∞ in this sense, together with an injective group homomorphism from G into H.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SimpleOvergroups.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SimpleOvergroups.lean; bytes 1077..1316
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_SimpleOvergroups

namespace OAI

namespace SimpleFInftyOvergroups

universe u

theorem main (G : Type u) [Group G] [Group.FG G]
    (hG : HasDecidableWordProblem G) :
    ∃ (H : Type u) (_ : Group H), Nontrivial H ∧ IsSimpleGroup H ∧
      HasTypeFInfty H ∧ ∃ f : G →* H, Function.Injective f := by
  sorry

end SimpleFInftyOvergroups
end OAI
