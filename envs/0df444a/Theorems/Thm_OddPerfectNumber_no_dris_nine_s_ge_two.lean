-- Prove2me | Theorems.Thm_OddPerfectNumber_no_dris_nine_s_ge_two
-- name    : OddPerfectNumber.no_dris_nine_s_ge_two
-- status  : Open
-- author  : @WillR
-- created : 2026-09-10T22:45:59.343991+00:00
-- url     : https://prove2.me/theorems/7e04435f-7248-4074-a140-0a117995be34
-- title:
--   Dris-index case k = 9 with s >= 2 is impossible
-- statement:
--   Let p be an odd prime with p congruent 1 mod 4, k = 9, m odd with p not dividing m, and s >= 2. Then 2m^2 = sigma(p^k)s and sigma(m^2) = p^k s cannot both hold. Non-extremal half of the k = 9 Dris split.
-- source:
--   J. A. B. Dris, The abundancy index of divisors of odd perfect numbers, Journal of Integer Sequences 15 (2012), Article 12.4.4, Section 2; Euler-form special-exponent subcase as recorded on the Odd Perfect Number Conjecture mission.

import Mathlib

namespace OddPerfectNumber

theorem no_dris_nine_s_ge_two (p k m s : Nat) (hp : p.Prime) (hp2 : p != 2)
    (hp4 : p % 4 = 1) (hk4 : k % 4 = 1) (hk9 : k = 9) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hs2 : 2 ≤ s) :
    ¬ (2 * m ^ 2 = (∑ d ∈ (p ^ k).divisors, d) * s ∧
      (∑ d ∈ (m ^ 2).divisors, d) = p ^ k * s) := by
  sorry

end OddPerfectNumber
