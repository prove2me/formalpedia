-- Prove2me | Theorems.Thm_OAI_QuantitativeVanDerWaerden_uniform_lower_bound
-- name    : OAI.QuantitativeVanDerWaerden.uniform_lower_bound
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:13.230004+00:00
-- url     : https://prove2.me/theorems/7e1d1090-0779-41fb-a276-ae1a532b25e3
-- statement:
--   The theorem states that there is a natural number K such that for every k ≥ K and every number of colors r ≥ 2, the quantity k raised to the power (1/100000)·k·⌊log₂ r⌋ (where the exponent uses the natural-number base-2 logarithm of r, cast to the reals) is strictly less than W(r,k). Here W(r,k) is the least positive N such that every coloring of the naturals ℕ with r colors (functions ℕ → Fin r) contains a monochromatic arithmetic progression of length k, meaning terms a, a+d, ..., a+(k−1)d with common difference d > 0, all of the same color, and with last term a+(k−1)d < N. W is defined as the infimum of this set, so it equals 0 if the set is empty, and the definition builds in no proof that the set is nonempty. The bound is uniform in r, since K does not depend on the number of colors, and the proof is admitted rather than supplied.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/QuantitativeVanDerWaerden.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/QuantitativeVanDerWaerden.lean; bytes 659..902
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_QuantitativeVanDerWaerden

namespace OAI

universe u

namespace QuantitativeVanDerWaerden

open Filter

/-- An absolute quantitative lower bound, uniform over all color counts. -/
theorem uniform_lower_bound :
    ∃ K : ℕ, ∀ k ≥ K, ∀ r ≥ 2,
      (k : ℝ) ^ ((1 / 100000 : ℝ) * k * (Nat.log 2 r : ℝ)) < (W r k : ℝ) := by
  sorry

end QuantitativeVanDerWaerden
end OAI
