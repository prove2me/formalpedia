-- Prove2me | Theorems.Thm_OddPerfectNumber_odd_order_dvd_half_of_p_minus_one
-- name    : OddPerfectNumber.odd_order_dvd_half_of_p_minus_one
-- status  : Disproved
-- author  : @WillR
-- created : 2026-09-30T17:47:41.17089+00:00
-- url     : https://prove2.me/theorems/e016fbd8-7f1d-4314-83aa-6a5ddb71fe84
-- title:
--   A nontrivial odd order modulo a prime p = 1 mod 4 divides (p-1)/2 and so is at most (p-1)/2
-- statement:
--   Let p be a prime congruent to 1 modulo 4 and t a natural number with p not dividing t whose multiplicative order modulo p is greater than 1. Then the order divides (p-1)/2, and consequently the order is at most (p-1)/2. Since the order divides the odd number two e plus one whenever p divides the associated geometric sum, this bounds the order from above, so the count two e plus one is at least the order and no odd order can exceed half of p minus one.

import Mathlib

namespace OddPerfectNumber

theorem odd_order_dvd_half_of_p_minus_one {p t : Nat} (hp : p.Prime) (hp4 : p % 4 = 1)
    (hpt : Not (Dvd.dvd p t)) (hord : 1 < orderOf (t : ZMod p)) :
    Dvd.dvd (orderOf (t : ZMod p)) ((p - 1) / 2) := by
  sorry

end OddPerfectNumber
