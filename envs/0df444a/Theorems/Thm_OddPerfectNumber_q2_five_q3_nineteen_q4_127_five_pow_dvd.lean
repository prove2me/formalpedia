-- Prove2me | Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_127_five_pow_dvd
-- name    : OddPerfectNumber.q2_five_q3_nineteen_q4_127_five_pow_dvd
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T01:50:40.662235+00:00
-- url     : https://prove2.me/theorems/4165a6a7-a361-4982-b817-e920fd97095b
-- title:
--   A sixfold five exponent forces five to the sixth power into the square
-- statement:
--   Under the q4=127 four-prime factorization, an exponent b≥6 on the 5-component forces 5^6 to divide m^2.
-- source:
--   Elementary power divisibility through the explicit factorization.

import Mathlib

namespace OddPerfectNumber

theorem q2_five_q3_nineteen_q4_127_five_pow_dvd (m a b c e : Nat)
    (hfac : m ^ 2 = 3 ^ a * 5 ^ b * 19 ^ c * 127 ^ e)
    (hb : 6 ≤ b) :
    5 ^ 6 ∣ m ^ 2 := by
  sorry

end OddPerfectNumber
