-- Prove2me | Theorems.Thm_OddPerfectNumber_odd_order_mod_four_le_lower_bound
-- name    : OddPerfectNumber.odd_order_mod_four_le_lower_bound
-- status  : Disproved
-- author  : @WillR
-- created : 2026-09-30T17:43:31.023558+00:00
-- url     : https://prove2.me/theorems/d865ae0f-f898-4b2a-93ce-163a21e259b8
-- title:
--   A nontrivial odd order modulo p = 1 mod 4 is at least (p-1)/4
-- statement:
--   Let p be a prime congruent to 1 modulo 4 and t a natural number with p not dividing t. If the multiplicative order of t modulo p is greater than 1 and divides the odd natural number n, then n is at least (p-1)/4. Equivalently an odd order greater than 1 can only be the odd part of p minus 1, so it is at least a quarter of p minus 1.

import Mathlib

namespace OddPerfectNumber

theorem odd_order_mod_four_le_lower_bound {p t n : Nat} (hp : p.Prime) (hp4 : p % 4 = 1)
    (hpt : Not (Dvd.dvd p t)) (hnodd : ¬ Even n)
    (hord : 1 < orderOf (t : ZMod p)) (hdiv : Dvd.dvd (orderOf (t : ZMod p)) n) :
    (p - 1) / 4 ≤ n := by
  sorry

end OddPerfectNumber
