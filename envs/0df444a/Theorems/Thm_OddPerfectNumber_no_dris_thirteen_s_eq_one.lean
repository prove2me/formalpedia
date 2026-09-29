-- Prove2me | Theorems.Thm_OddPerfectNumber_no_dris_thirteen_s_eq_one
-- name    : OddPerfectNumber.no_dris_thirteen_s_eq_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-10T22:45:48.634579+00:00
-- url     : https://prove2.me/theorems/5ceed642-ba34-4061-914c-16f67437ee2c
-- title:
--   Dris-index case k >= 13 with s = 1 is impossible
-- statement:
--   Let p be an odd prime with p congruent 1 mod 4, k congruent 1 mod 4 with k >= 13, m odd with p not dividing m, and s = 1. Then 2m^2 = sigma(p^k)s and sigma(m^2) = p^k s cannot both hold. Extremal-index half of the k >= 13 Dris split.
-- source:
--   J. A. B. Dris, The abundancy index of divisors of odd perfect numbers, Journal of Integer Sequences 15 (2012), Article 12.4.4, Section 2; Euler-form special-exponent subcase as recorded on the Odd Perfect Number Conjecture mission.

import Mathlib

namespace OddPerfectNumber

theorem no_dris_thirteen_s_eq_one (p k m s : Nat) (hp : p.Prime) (hp2 : p != 2)
    (hp4 : p % 4 = 1) (hk4 : k % 4 = 1) (hk13 : 13 ≤ k) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hs1 : s = 1) :
    ¬ (2 * m ^ 2 = (∑ d ∈ (p ^ k).divisors, d) * s ∧
      (∑ d ∈ (m ^ 2).divisors, d) = p ^ k * s) := by
  sorry

end OddPerfectNumber
