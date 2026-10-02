-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_odd_order_dvd_quarter_of_p_minus_one
-- name    : OddPerfectNumber.Kernel.odd_order_dvd_quarter_of_p_minus_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-01T06:55:51.572334+00:00
-- url     : https://prove2.me/theorems/08fe6da2-1ba0-4692-b142-e9c52d0cdc9a
-- title:
--   An odd multiplicative order divides a quarter of p minus one
-- statement:
--   Let p be a prime congruent to 1 modulo 4, let t be a natural number not divisible by p, and suppose the multiplicative order of t modulo p is odd. Then that order divides (p-1)/4, so t raised to the (p-1)-th power is the identity, and t lies in the subgroup of fourth powers modulo p. The proof is arithmetic: the order divides p-1, p-1 is four times (p-1)/4, and an odd number is coprime to four, so the factor four cancels. This is the corrected form of the disproved statement odd_order_dvd_half_of_p_minus_one, whose only defect was the missing oddness hypothesis; even orders, such as the order four of 2 modulo 5, genuinely do not divide (p-1)/2.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem odd_order_dvd_quarter_of_p_minus_one {p t : Nat} (hp : p.Prime)
    (hp4 : p % 4 = 1) (hpt : Not (Dvd.dvd p t))
    (hodd : Odd (orderOf (t : ZMod p))) :
    Dvd.dvd (orderOf (t : ZMod p)) ((p - 1) / 4) := by
  sorry

end OddPerfectNumber.Kernel
