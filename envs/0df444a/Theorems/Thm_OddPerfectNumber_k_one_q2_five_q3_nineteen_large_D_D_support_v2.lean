-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_large_D_D_support_v2
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_large_D_D_support_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-15T17:32:07.218884+00:00
-- url     : https://prove2.me/theorems/e67054df-6290-4544-a184-6cae37f36bc8
-- title:
--   Canonical q3=19 support restriction for D v2
-- statement:
--   If the q2=5,q3=19 square factorization is accepted and D divides m², every prime divisor of D is one of the four support primes.
-- source:
--   Prime-divisor descent through the four-factor square identity; no finite enumeration or source obstruction is assumed.

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_large_D_D_support_v2 (m a b c e D q4 : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 19 ^ (2*c) * q4 ^ (2*e))
    (hDdvd : D ∣ m ^ 2)
    (hq4prime : q4.Prime) :
    ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 19 ∨ r = q4 := by
  sorry

end OddPerfectNumber
