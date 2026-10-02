-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_geom_sum_dvd_order_dvd_odd_count
-- name    : OddPerfectNumber.Kernel.geom_sum_dvd_order_dvd_odd_count
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T17:14:58.718871+00:00
-- url     : https://prove2.me/theorems/e5d78741-2c45-4973-895e-0ffeaeb7169e
-- title:
--   A prime divisor of a geometric sum gives an order dividing the odd count
-- statement:
--   Let p be a prime and q and e natural numbers. If p divides the sum of the first two e plus one powers of q, then the multiplicative order of q in the units modulo p divides two e plus one.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem geom_sum_dvd_order_dvd_odd_count {p q e : Nat} (hp : p.Prime)
    (hdvd : Dvd.dvd p (∑ i ∈ Finset.range (2 * e + 1), q ^ i)) :
    Dvd.dvd (orderOf (q : ZMod p)) (2 * e + 1) := by
  sorry

end OddPerfectNumber.Kernel
