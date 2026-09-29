-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_seventeen_D289_order_certificates_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_seventeen_D289_order_certificates_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T10:41:28.725537+00:00
-- url     : https://prove2.me/theorems/fc68e6c3-c569-42b0-abe2-06a02cbdb3bc
-- title:
--   q17 D289 order certificates
-- statement:
--   The multiplicative orders of 3 modulo the nine D=289 residual primes take the listed exact values.
-- source:
--   Finite order certificates feeding the q17 residual leaf; half-exponent convention not involved.

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_seventeen_D289_order_certificates_v1 :
    orderOf (3 : ZMod 31) = 30 ∧ orderOf (3 : ZMod 61) = 10 ∧ orderOf (3 : ZMod 151) = 50 ∧ orderOf (3 : ZMod 181) = 45 ∧ orderOf (3 : ZMod 211) = 210 ∧ orderOf (3 : ZMod 241) = 120 ∧ orderOf (3 : ZMod 271) = 30 ∧ orderOf (3 : ZMod 331) = 330 ∧ orderOf (3 : ZMod 421) = 105 := by
  sorry

end OddPerfectNumber
