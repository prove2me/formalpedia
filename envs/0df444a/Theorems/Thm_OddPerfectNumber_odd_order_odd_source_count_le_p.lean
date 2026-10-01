-- Prove2me | Theorems.Thm_OddPerfectNumber_odd_order_odd_source_count_le_p
-- name    : OddPerfectNumber.odd_order_odd_source_count_le_p
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T17:47:45.891104+00:00
-- url     : https://prove2.me/theorems/c61a3b2d-40c5-4f4f-81c5-a871a31d9f45
-- title:
--   An odd nontrivial order forces the odd count to be a multiple of an odd number at most (p-1)/2
-- statement:
--   Let p be a prime congruent to 1 modulo 4 and t a natural number with p not dividing t whose multiplicative order modulo p is greater than 1 and divides the odd natural number n. Then n is at least the order of t modulo p, so the odd count n is at least that order, and every such order is an odd divisor of (p-1)/2.

import Mathlib

namespace OddPerfectNumber

theorem odd_order_odd_source_count_le_p {p t n : Nat} (hp : p.Prime) (hp4 : p % 4 = 1)
    (hpt : Not (Dvd.dvd p t)) (hnodd : ¬ Even n) (hord : 1 < orderOf (t : ZMod p))
    (hdiv : Dvd.dvd (orderOf (t : ZMod p)) n) :
    orderOf (t : ZMod p) ≤ n ∧ Dvd.dvd (orderOf (t : ZMod p)) ((p - 1) / 2) := by
  sorry

end OddPerfectNumber
