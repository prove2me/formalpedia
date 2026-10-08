-- Prove2me | Theorems.Thm_OAI_FiniteAlgebraicEnvelopes_main
-- name    : OAI.FiniteAlgebraicEnvelopes.main
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:40.280984+00:00
-- url     : https://prove2.me/theorems/e134023a-5966-4913-9e27-582bdc8c6e2e
-- statement:
--   The theorem states that for any group G (in universe u) that is finitely generated, G has a decidable word problem if and only if G embeds in a finitely presented simple group. Here, having a decidable word problem means there exist a natural number n and a map from Fin n into G whose images generate G (the subgroup they generate is all of G), such that the set of words, namely finite lists of pairs (i, b) with i in Fin n and b a Boolean sign, that evaluate to the identity is a computable predicate; a letter (i, true) evaluates to the generator g_i, a letter (i, false) to its inverse, and a word evaluates to the product of its letters in order. Embedding in a finitely presented simple group means there exists a group H in the same universe, which is finitely presented and simple, together with an injective group homomorphism from G into H. The statement is admitted in the source without proof.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/BooneHigman.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/BooneHigman.lean; bytes 1021..1198
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_BooneHigman

namespace OAI

namespace FiniteAlgebraicEnvelopes

universe u

theorem main (GroupType : Type u) [Group GroupType] [Group.FG GroupType] :
    HasDecidableWordProblem GroupType ↔ EmbedsInFinitelyPresentedSimpleGroup GroupType := by
  sorry

end FiniteAlgebraicEnvelopes
end OAI
