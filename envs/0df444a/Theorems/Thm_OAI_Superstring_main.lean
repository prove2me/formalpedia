-- Prove2me | Theorems.Thm_OAI_Superstring_main
-- name    : OAI.Superstring.main
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:27.773515+00:00
-- url     : https://prove2.me/theorems/cdd07c08-48de-4395-95f4-74a24f33d3bd
-- statement:
--   The theorem states that there is a function f sending each instance (a finite list of words, where a word is a list of symbols and a symbol is a finite list of bits) to a word, such that two things hold. First, f has a polynomial implementation: there is a deterministic multi-stack Turing machine (a TM2 machine) computing f in polynomial time, measured in bit-level steps in the length of the encoded input, where the instance is encoded as a bit string with prefix markers (false before each list element, true to end each list) and the output word is encoded likewise, and every stack alphabet of the machine is finite. Second, for every instance S, f(S) is a common superstring of S, meaning every word of S occurs in f(S) as a contiguous block of consecutive symbols (the empty word always qualifies), and the length of f(S) in symbols is at most 2 times opt(S), where opt(S) is the least length in symbols of any common superstring of S. This is a factor-two approximation guarantee for shortest common superstring, stated as admitted rather than proved.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/Superstring.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/Superstring.lean; bytes 1214..1522
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_Superstring

namespace OAI

namespace Superstring

/-- The deterministic algorithm with its exact finite-alphabet bit-machine
certificate, contiguous coverage, and factor-two bound in symbols. -/
theorem main : ∃ f : Instance → Word,
    HasPolynomialImplementation f ∧
    ∀ S, IsCommonSuperstring S (f S) ∧ (f S).length ≤ 2 * opt S := by
  sorry

end Superstring
end OAI
