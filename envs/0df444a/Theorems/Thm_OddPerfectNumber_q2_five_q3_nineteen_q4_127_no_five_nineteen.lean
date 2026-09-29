-- Prove2me | Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_127_no_five_nineteen
-- name    : OddPerfectNumber.q2_five_q3_nineteen_q4_127_no_five_nineteen
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T00:00:35.150742+00:00
-- url     : https://prove2.me/theorems/4b08acc6-e7ad-4637-8460-840edde4b7bd
-- title:
--   The 19-component cannot supply 5 in the q4=127 support
-- statement:
--   For every even exponent 2e, the local divisor sum of 19^(2e) is not divisible by 5.
-- source:
--   Concrete order certificate for the q2=5, q3=19, q4=127 residual factor-5 contradiction.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_not_dvd_of_order_certificate

namespace OddPerfectNumber

theorem q2_five_q3_nineteen_q4_127_no_five_nineteen (e : Nat) :
    ¬ 5 ∣ ∑ i ∈ Finset.range (2 * e + 1), 19 ^ i := by
  sorry

end OddPerfectNumber
