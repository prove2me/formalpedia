-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_b_one_D3_q4_31_absurd_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentynine_b_one_D3_q4_31_absurd_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T07:40:26.297976+00:00
-- url     : https://prove2.me/theorems/1fd40af8-3992-4bc7-9546-ca59f76c8ae8
-- title:
--   q3=29 b=1 D=3 terminal via Euler separation
-- statement:
--   D=3 forces p=5 dividing m, against Euler separation.
-- source:
--   Closes the D=3 corner of the b=1 lower bound.

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentynine_b_one_D3_q4_31_absurd_v1 (D p sigma m a b c e q4 : Nat)
    (hrel : D * sigma = p * m ^ 2) (hD : D = 3) (hp_eq : p = 2 * D - 1)
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hq4eq : q4 = 31)
    (hpm : ¬ p ∣ m) (h5mem : 5 ∈ (m ^ 2).primeFactors) :
    False := by
  sorry

end OddPerfectNumber
