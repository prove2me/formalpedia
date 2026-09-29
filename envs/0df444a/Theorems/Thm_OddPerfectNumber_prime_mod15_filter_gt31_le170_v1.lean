-- Prove2me | Theorems.Thm_OddPerfectNumber_prime_mod15_filter_gt31_le170_v1
-- name    : OddPerfectNumber.prime_mod15_filter_gt31_le170_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T16:48:30.62802+00:00
-- url     : https://prove2.me/theorems/608a239f-3f48-450b-9664-e3b0b8a638d0
-- title:
--   Prime q4 with 31<q4<=170 and q4=1 mod 15 is 61 or 151
-- statement:
--   A prime q4 with 31<q4<=170 and q4 congruent 1 mod 15 is 61 or 151, serving the q31 D15 b=1 residual step.

import Mathlib

namespace OddPerfectNumber

theorem prime_mod15_filter_gt31_le170_v1 (q4 : Nat)
    (hprime : q4.Prime) (hlo : 31 < q4) (hmod : q4 % 15 = 1) (hhi : q4 ≤ 170) :
    q4 = 61 ∨ q4 = 151 := by
  sorry

end OddPerfectNumber
