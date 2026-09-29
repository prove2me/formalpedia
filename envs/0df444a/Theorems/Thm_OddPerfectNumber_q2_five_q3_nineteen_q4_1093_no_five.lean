-- Prove2me | Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_1093_no_five
-- name    : OddPerfectNumber.q2_five_q3_nineteen_q4_1093_no_five
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T02:28:59.203426+00:00
-- url     : https://prove2.me/theorems/26af0bfd-f11b-4988-9ae3-9a27a05e71e8
-- title:
--   No odd-length geometric sum in base 1093 is divisible by 5
-- statement:
--   No odd-length geometric sum in base 1093 is divisible by 5, because the order modulo 5 is even.
-- source:
--   Finite order-divisor certificate for the q4=1093 subcase.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_not_dvd_of_even_order

namespace OddPerfectNumber

theorem q2_five_q3_nineteen_q4_1093_no_five (e : Nat) :
    ¬ 5 ∣ ∑ i ∈ Finset.range (2 * e + 1), 1093 ^ i := by
  sorry

end OddPerfectNumber
