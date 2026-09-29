-- Prove2me | Theorems.Thm_OddPerfectNumber_geom_sum_dvd_order_dvd_v1
-- name    : OddPerfectNumber.geom_sum_dvd_order_dvd_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T17:03:21.78513+00:00
-- url     : https://prove2.me/theorems/8d803f36-9d46-4571-9d28-3a0432e92509
-- title:
--   Divisibility of a geometric sum bounds the multiplicative order
-- statement:
--   If a prime q divides the length-(n+1) geometric sum in base b, the multiplicative order of b mod q divides n+1. Reusable source bridge for the q17/q31 finite branches.

import Mathlib

namespace OddPerfectNumber

theorem geom_sum_dvd_order_dvd_v1 (b q n : Nat)
    (hq : q.Prime) (hb : 1 ≤ b)
    (hdiv : q ∣ ∑ i ∈ Finset.range (n + 1), b ^ i) :
    orderOf (b : ZMod q) ∣ n + 1 := by
  sorry

end OddPerfectNumber
