-- Prove2me | Theorems.Thm_OddPerfectNumber_no_dris_thirteen_s_ge_two
-- name    : OddPerfectNumber.no_dris_thirteen_s_ge_two
-- status  : Open
-- author  : @WillR
-- created : 2026-09-10T22:46:00.550212+00:00
-- url     : https://prove2.me/theorems/ed4992b6-2881-4868-a905-d38e427a13f7
-- title:
--   Dris-index case k >= 13 with s >= 2 is impossible
-- statement:
--   Let p be an odd prime with p congruent 1 mod 4, k congruent 1 mod 4 with k >= 13, m odd with p not dividing m, and s >= 2. Then 2m^2 = sigma(p^k)s and sigma(m^2) = p^k s cannot both hold. Non-extremal half of the k >= 13 Dris split.
-- source:
--   J. A. B. Dris, The abundancy index of divisors of odd perfect numbers, Journal of Integer Sequences 15 (2012), Article 12.4.4, Section 2; Euler-form special-exponent subcase as recorded on the Odd Perfect Number Conjecture mission.

import Mathlib

namespace OddPerfectNumber

theorem no_dris_thirteen_s_ge_two (p k m s : Nat) (hp : p.Prime) (hp2 : p != 2)
    (hp4 : p % 4 = 1) (hk4 : k % 4 = 1) (hk13 : 13 ≤ k) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hs2 : 2 ≤ s) :
    ¬ (2 * m ^ 2 = (∑ d ∈ (p ^ k).divisors, d) * s ∧
      (∑ d ∈ (m ^ 2).divisors, d) = p ^ k * s) := by
  sorry

end OddPerfectNumber
