-- Prove2me | Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_547_no_five
-- name    : OddPerfectNumber.q2_five_q3_nineteen_q4_547_no_five
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T02:29:01.098975+00:00
-- url     : https://prove2.me/theorems/c1259034-57d4-48b4-bd5c-0e85538f64c4
-- title:
--   No odd-length geometric sum in base 547 is divisible by 5
-- statement:
--   No odd-length geometric sum in base 547 is divisible by 5, because the order modulo 5 is even.
-- source:
--   Finite order-divisor certificate for the p=1093, q4=547 subcase.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_not_dvd_of_even_order

namespace OddPerfectNumber

theorem q2_five_q3_nineteen_q4_547_no_five (e : Nat) :
    ¬ 5 ∣ ∑ i ∈ Finset.range (2 * e + 1), 547 ^ i := by
  sorry

end OddPerfectNumber
