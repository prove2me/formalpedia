-- Prove2me | Theorems.Thm_OddPerfectNumber_prime_mod15_filter_gt17_lt500_v1
-- name    : OddPerfectNumber.prime_mod15_filter_gt17_lt500_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T14:05:51.461085+00:00
-- url     : https://prove2.me/theorems/83dd4748-c6ed-436a-b42d-9135e5dd46d4
-- title:
--   prime 1-mod-15 filter in (17,500)
-- statement:
--   A prime q4 with 17<q4<500 and q4=1 mod 15 is one of 31,61,151,181,211,241,271,331,421.

import Mathlib

namespace OddPerfectNumber

theorem prime_mod15_filter_gt17_lt500_v1 (q4 : Nat)
    (hprime : q4.Prime) (hlo : 17 < q4) (hmod : q4 % 15 = 1) (hhi : q4 < 500) :
    q4 = 31 ∨ q4 = 61 ∨ q4 = 151 ∨ q4 = 181 ∨ q4 = 211 ∨ q4 = 241 ∨ q4 = 271 ∨ q4 = 331 ∨ q4 = 421 := by
  sorry

end OddPerfectNumber
