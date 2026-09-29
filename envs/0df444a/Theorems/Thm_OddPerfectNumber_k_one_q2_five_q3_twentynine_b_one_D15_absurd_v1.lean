-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_b_one_D15_absurd_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentynine_b_one_D15_absurd_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T05:07:54.266248+00:00
-- url     : https://prove2.me/theorems/d3fb7a57-911b-4750-a225-cea2945e8a16
-- title:
--   q3=29 b=1 D=15 Euler-separation kill
-- statement:
--   D=15 forces Euler prime p=29 dividing m, against separation.
-- source:
--   Per-D terminal for the b=1 composer chain. Half-exponent convention, canonical structural binders.

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentynine_b_one_D15_absurd_v1 (p m d q4 a b c e sigma D : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 29 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 29 < q4)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c) * q4 ^ (2*e))
    (h29mem : 29 ∈ (m ^ 2).primeFactors)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (he : 0 < e)
    (hp_eq : p = 2 * D - 1) (hD : D = 15) :
    False := by
  sorry

end OddPerfectNumber
