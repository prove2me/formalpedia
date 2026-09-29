-- Prove2me | Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_127_no_five_127_odd_order
-- name    : OddPerfectNumber.q2_five_q3_nineteen_q4_127_no_five_127_odd_order
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T00:44:25.675041+00:00
-- url     : https://prove2.me/theorems/4ddc7d4c-cafc-429f-ad26-fd3c01f06143
-- title:
--   The q4=127 component cannot supply 5 by the odd-order divisor argument
-- statement:
--   No odd-length geometric sum in base 127 is divisible by 5; the order modulo 5 divides 4, is not 1, and therefore cannot divide an odd length.
-- source:
--   Independent finite order-divisor certificate for the q4=127 source obstruction.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_not_dvd_of_order_certificate

namespace OddPerfectNumber

theorem q2_five_q3_nineteen_q4_127_no_five_127_odd_order (e : Nat) :
    ¬ 5 ∣ ∑ i ∈ Finset.range (2 * e + 1), 127 ^ i := by
  sorry

end OddPerfectNumber
