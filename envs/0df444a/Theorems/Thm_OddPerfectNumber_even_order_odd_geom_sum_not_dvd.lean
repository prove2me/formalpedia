-- Prove2me | Theorems.Thm_OddPerfectNumber_even_order_odd_geom_sum_not_dvd
-- name    : OddPerfectNumber.even_order_odd_geom_sum_not_dvd
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T11:51:42.437325+00:00
-- url     : https://prove2.me/theorems/9073a0c7-03fd-4e8a-a47b-ccc5f573a4ca
-- title:
--   even order cannot divide an odd-length geometric sum
-- statement:
--   If the order of b mod p is even and n is odd, p does not divide the length-n base-b geometric sum.
-- source:
--   Shared obstruction for q17 D225 (p=449) and D289 (p=577): all support orders even, all sigma lengths odd.

import Mathlib

namespace OddPerfectNumber

theorem even_order_odd_geom_sum_not_dvd (b p n : Nat) (heven : Even (orderOf (b : ZMod p)))
    (hodd : Odd n) : ¬ (p ∣ (Finset.range n).sum (fun i => b ^ i)) := by
  sorry

end OddPerfectNumber
