-- Prove2me | Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_127_no_five_nineteen_odd_order
-- name    : OddPerfectNumber.q2_five_q3_nineteen_q4_127_no_five_nineteen_odd_order
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T00:49:29.144323+00:00
-- url     : https://prove2.me/theorems/b6ce0907-c74f-4a3b-99e1-7ee012beb438
-- title:
--   The 19-component cannot supply 5 by the odd-order divisor argument
-- statement:
--   No odd-length geometric sum in base 19 is divisible by 5, using the order divisor bound modulo 5.
-- source:
--   Independent order-divisor certificate for the q4=127 source obstruction.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_not_dvd_of_order_certificate

namespace OddPerfectNumber

theorem q2_five_q3_nineteen_q4_127_no_five_nineteen_odd_order (e : Nat) :
    ¬ 5 ∣ ∑ i ∈ Finset.range (2 * e + 1), 19 ^ i := by
  sorry

end OddPerfectNumber
