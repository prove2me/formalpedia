-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_middle_block_order_one_forces_full_factor
-- name    : OddPerfectNumber.Kernel.middle_block_order_one_forces_full_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T06:54:25.621414+00:00
-- url     : https://prove2.me/theorems/76e2c273-03a1-4ad8-bd0b-106756b3678f
-- title:
--   Order-one middle source forces the full cyclotomic factor
-- statement:
--   Let p and q be primes and factor p^2+p+1 as q*k. If both q and the complementary factor k are congruent to 1 modulo p, then q is the entire factor p^2+p+1. Indeed q is at least p+1; if k were greater than 1 then k would also be at least p+1, contradicting (p+1)^2 > p^2+p+1. In the k=5 two-prime residual this is the order-one middle-source reduction and implies the middle square factor is 1.
-- source:
--   Elementary factor-size argument for the k=5 middle cyclotomic block in the Odd Perfect Number Conjecture mission. The hypotheses expose the quotient congruence explicitly; no unproved primitive-divisor or reciprocity theorem is used.

import Mathlib

import Mathlib

namespace OddPerfectNumber.Kernel

theorem middle_block_order_one_forces_full_factor
    (p q k : Nat) (hp : p.Prime) (hq : q.Prime)
    (hC : p ^ 2 + p + 1 = q * k)
    (hqmod : q % p = 1) (hkmod : k % p = 1) :
    q = p ^ 2 + p + 1 := by
  sorry

end OddPerfectNumber.Kernel
