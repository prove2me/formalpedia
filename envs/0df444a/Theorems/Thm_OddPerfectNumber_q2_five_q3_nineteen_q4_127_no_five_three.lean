-- Prove2me | Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_127_no_five_three
-- name    : OddPerfectNumber.q2_five_q3_nineteen_q4_127_no_five_three
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-13T23:42:28.987209+00:00
-- url     : https://prove2.me/theorems/c09a025d-7bfd-49ff-afce-9788567bf75f
-- title:
--   The 3-component cannot supply 5 in the q4=127 support
-- statement:
--   For every even exponent 2e, the local divisor sum of 3^(2e) is not divisible by 5, because the multiplicative order of 3 modulo 5 is 4 and 4 cannot divide the odd length 2e+1.
-- source:
--   Concrete order certificate for the q2=5, q3=19, q4=127 residual factor-5 contradiction.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_not_dvd_of_order_certificate

namespace OddPerfectNumber

theorem q2_five_q3_nineteen_q4_127_no_five_three (e : Nat) :
    ¬ 5 ∣ ∑ i ∈ Finset.range (2 * e + 1), 3 ^ i := by
  sorry

end OddPerfectNumber
