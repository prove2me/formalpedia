-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_two_prime_middle_block_prime_not_euler_source
-- name    : OddPerfectNumber.Kernel.two_prime_middle_block_prime_not_euler_source
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-04T00:26:00.590709+00:00
-- url     : https://prove2.me/theorems/35881fea-e1a0-4c59-a638-c09217fa470c
-- title:
--   A prime whose multiplicative order modulo the Euler prime does not divide (p-1)/4 cannot supply p through a three-term divisor sum
-- statement:
--   Let p be a prime that is 1 modulo 4 and qC a natural number whose multiplicative order in the group ZMod p does not divide (p-1)/4. Then p does not divide the three-term sum 1 + qC + qC squared. This is the order-theoretic restriction behind excluding the middle cyclotomic block prime as an incoming source of the Euler prime in the two-prime k=5 branch.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem two_prime_middle_block_prime_not_euler_source {p qC : Nat} (hp : p.Prime)
    (hp5 : p % 4 = 1) (hord : Not (Dvd.dvd (orderOf (qC : ZMod p)) ((p - 1) / 4))) :
    Not (Dvd.dvd p (1 + qC + qC ^ 2)) := by
  sorry

end OddPerfectNumber.Kernel
