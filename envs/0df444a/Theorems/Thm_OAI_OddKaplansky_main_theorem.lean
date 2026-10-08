-- Prove2me | Theorems.Thm_OAI_OddKaplansky_main_theorem
-- name    : OAI.OddKaplansky.main_theorem
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:58.277757+00:00
-- url     : https://prove2.me/theorems/4d62bd08-ecb0-4f88-a15c-5f908ad62bd0
-- statement:
--   The theorem states that the defined proposition MainClaim holds. Here sourceM is the central binomial coefficient C(1200,600), and sourcePrime is the smallest prime factor of (sourceM!)²+1. MainClaim asserts that this number p is prime and odd, and that there exist a finite field K of characteristic p with exactly p⁴ elements and a finitely generated group G containing a nontrivial element of finite order, together with two elements a and b of the group algebra K[G] such that ab = 1 but ba ≠ 1. Moreover, for the map cellular(b) sending x : G → K to g ↦ Σ_u b(u)·x(g·u), the sum running over the support of b, this map is injective but not surjective. The formal statement is admitted in the source rather than proved here.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/OddKaplansky.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/OddKaplansky.lean; bytes 797..843
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_OddKaplansky

namespace OAI

namespace OddKaplansky

noncomputable section

theorem main_theorem : MainClaim := by
  sorry

end
end OddKaplansky
end OAI
