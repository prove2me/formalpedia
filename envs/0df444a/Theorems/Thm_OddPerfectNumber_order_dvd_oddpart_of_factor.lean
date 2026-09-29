-- Prove2me | Theorems.Thm_OddPerfectNumber_order_dvd_oddpart_of_factor
-- name    : OddPerfectNumber.order_dvd_oddpart_of_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-13T13:29:16.55202+00:00
-- url     : https://prove2.me/theorems/ee097dda-f15b-4cc4-9765-3be22ffd0e3c
-- title:
--   Odd order divides the odd part
-- statement:
--   If an order divides p minus one, p minus one is factored as a power of two times an odd part, and the order is odd, then the order divides the odd part.

import Mathlib

theorem OddPerfectNumber.order_dvd_oddpart_of_factor {p q k u : Nat}
    (hfactor : p - 1 = 2 ^ k * u)
    (hord : orderOf (q : ZMod p) ∣ p - 1)
    (hodd : Odd (orderOf (q : ZMod p))) :
    orderOf (q : ZMod p) ∣ u := by sorry
