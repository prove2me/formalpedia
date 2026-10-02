-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_odd_order_dvd_pow_card_sub_one
-- name    : OddPerfectNumber.Kernel.odd_order_dvd_pow_card_sub_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-01T01:13:18.652568+00:00
-- url     : https://prove2.me/theorems/254ae6b2-eaa6-4234-b55b-1a93f9d57a7b
-- title:
--   A residue of odd multiplicative order has its order as an exponent
-- statement:
--   Let p be a prime and t a natural number with p not dividing t, and suppose the multiplicative order of t modulo p is odd. Then t raised to the order of t is congruent to 1 modulo p. Together with the accepted OddPerfectNumber.geom_sum_dvd_implies_order_dvd, which shows that any prime dividing a geometric sum 1 + t + ... + t^(2e) has order dividing the odd number 2e+1, this packages the first-equation fact that every sigma-source of a prime has odd multiplicative order at that prime.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem odd_order_dvd_pow_card_sub_one {p t : Nat} (hp : p.Prime)
    (hpt : Not (Dvd.dvd p t))
    (hodd : Odd (orderOf (t : ZMod p))) :
    (t : ZMod p) ^ (orderOf (t : ZMod p)) = 1 := by
  sorry

end OddPerfectNumber.Kernel
