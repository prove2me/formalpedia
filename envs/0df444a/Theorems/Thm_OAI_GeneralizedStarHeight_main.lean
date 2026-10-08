-- Prove2me | Theorems.Thm_OAI_GeneralizedStarHeight_main
-- name    : OAI.GeneralizedStarHeight.main
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:42.496947+00:00
-- url     : https://prove2.me/theorems/ece5a21e-ed22-4ce7-96ac-962ce0317646
-- statement:
--   Generalized regular expressions over an alphabet are built from the constants 0 (empty language) and 1 (the language containing only the empty word), single letters, binary union, binary concatenation, complement, and Kleene star. Each expression denotes a language: union is union of languages, concatenation is product of languages, complement is the set-theoretic complement among all words, and star is the Kleene star. The star height of an expression is 0 for 0, 1 and letters, the maximum of the two heights for union and concatenation, unchanged under complement, and one more than the height of the argument under star; so complement is free and only nested stars count. HasHeightAtMost(L,n) says some expression denotes L and has height at most n. The theorem states that, for any finite alphabet (in an arbitrary universe) and any regular language L over it, L has generalized star height at most 3, that is, L is denoted by some expression with complement allowed and star nesting depth at most 3. The theorem is admitted in the source rather than proved there.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/GeneralizedStarHeight.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/GeneralizedStarHeight.lean; bytes 1198..1331
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_GeneralizedStarHeight

namespace OAI

namespace GeneralizedStarHeight

universe u

theorem main {Alphabet : Type u} [Finite Alphabet] (L : Language Alphabet) (hL : L.IsRegular) :
    HasHeightAtMost L 3 := by
  sorry

end GeneralizedStarHeight
end OAI
