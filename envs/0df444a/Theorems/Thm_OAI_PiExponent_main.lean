-- Prove2me | Theorems.Thm_OAI_PiExponent_main
-- name    : OAI.PiExponent.main
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:03.369565+00:00
-- url     : https://prove2.me/theorems/5f472fc7-4c4f-407f-ac60-4bbaa407d996
-- statement:
--   The theorem states that two facts hold about approximating π by rationals, combined in one conjunction. First, for every real ν>2 there is an integer Q≥2 such that for all integers p and q with q≥Q, the distance |π − p/q| is at least q^(−ν); in other words, π has no rational approximations beating exponent ν once the denominator is large enough. Second, the supremum of the set of positive real ν for which there are infinitely many rationals r with denominator at least 2, with r different from π (the distance |π − r| being positive), and with |π − r| < (den r)^(−ν), equals exactly 2. Here den r is the reduced denominator of r. So the irrationality exponent of π is stated to be 2.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PiExponent.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/PiExponent.lean; bytes 53..400
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace PiExponent

theorem main :
  (∀ ν : ℝ, 2 < ν → ∃ Q : ℤ, 2 ≤ Q ∧
    ∀ p q : ℤ, Q ≤ q →
      (q : ℝ) ^ (-ν) ≤ |Real.pi - (p : ℝ) / (q : ℝ)|) ∧
  sSup {ν : ℝ | 0 < ν ∧
    Set.Infinite {r : ℚ | 2 ≤ r.den ∧
      0 < |Real.pi - (r : ℝ)| ∧
      |Real.pi - (r : ℝ)| < (r.den : ℝ) ^ (-ν)}} = 2 := by
  sorry

end PiExponent
end OAI
