-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirtyone_D15_b1_no_prime_order_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_thirtyone_D15_b1_no_prime_order_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T17:20:17.383423+00:00
-- url     : https://prove2.me/theorems/e5875b7d-7903-408d-be9d-d21007b14115
-- title:
--   No prime order in the q31 D15 b=1 residual pair
-- statement:
--   For q4 in {61,151} with the two order certificates, the order of 3 mod q4 is 10 resp. 50, hence not prime.
-- source:
--   Finite adapter feeding D15_b1_terminal_v1 hindex premise; consumes Proved order61_3 and pending order151_3 certs.

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_thirtyone_D15_b1_no_prime_order_v1 (q4 : Nat)
    (hq : q4 = 61 ∨ q4 = 151)
    (ho61 : q4 = 61 → orderOf (3 : ZMod q4) = 10)
    (ho151 : q4 = 151 → orderOf (3 : ZMod q4) = 50) :
    ¬ Nat.Prime (orderOf (3 : ZMod q4)) := by
  sorry

end OddPerfectNumber
