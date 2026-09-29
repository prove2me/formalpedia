-- Prove2me | Theorems.Thm_OddPerfectNumber_prime_power_sigma_euler_upper_bound
-- name    : OddPerfectNumber.prime_power_sigma_euler_upper_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-13T11:04:50.086585+00:00
-- url     : https://prove2.me/theorems/d2496ca9-c3d2-4f8e-9bed-4043d1eb5b38
-- title:
--   Integer upper bound for a prime-power divisor sum
-- statement:
--   For q greater than one, the geometric prime-power divisor sum satisfies the integer inequality (q−1)(1+q+⋯+q^a)<q^(a+1). This is the division-free form of the standard prime-power abundancy upper bound.
-- source:
--   Elementary telescoping identity for geometric sums, using the accepted OddPerfectNumber.geom_mul_sub_one theorem.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_mul_sub_one

namespace OddPerfectNumber

theorem prime_power_sigma_euler_upper_bound (q a : Nat)
    (hq : 1 < q) :
    (q - 1) * (∑ i ∈ Finset.range (a + 1), q ^ i) < q ^ (a + 1) := by sorry

end OddPerfectNumber
