-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_seventeen_D289_q4_lt_500_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_seventeen_D289_q4_lt_500_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T14:10:22.153824+00:00
-- url     : https://prove2.me/theorems/a88cf068-463c-4634-ba5f-b4ddf0aff3dd
-- title:
--   q17 D289 abundance cut q4<500
-- statement:
--   From D=289, p=577 and crude geometric-sum upper bounds, the fourth prime is below 500.

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_seventeen_D289_q4_lt_500_v1 (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 17 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 17 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hp_eq : p = 2 * D - 1) (hp : p.Prime)
    (hq4 : q4.Prime) (hq4gt : 17 < q4)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (he : 1 ≤ e)
    (hD : D = 289) :
    q4 < 500 := by
  sorry

end OddPerfectNumber
