-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_p31_hprod_odd_square_absurd
-- name    : OddPerfectNumber.k_one_p31_hprod_odd_square_absurd
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-13T22:40:01.87699+00:00
-- url     : https://prove2.me/theorems/1f0d654d-6623-4868-9079-887041203b98
-- title:
--   Euler prime 31 is impossible in the odd square product equation
-- statement:
--   If p=31, the product equation makes 16 divide the odd square m^2, hence 2 divides m, contradicting oddness.
-- source:
--   Substitute p=31 in the product equation to obtain 16 | m^2. A prime divisor of a square divides its base, so 2 | m, contradicting Odd m.

import Mathlib

namespace OddPerfectNumber

theorem k_one_p31_hprod_odd_square_absurd (p m d : Nat)
    (hm : Odd m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hp31 : p = 31) :
    False := by sorry

end OddPerfectNumber
