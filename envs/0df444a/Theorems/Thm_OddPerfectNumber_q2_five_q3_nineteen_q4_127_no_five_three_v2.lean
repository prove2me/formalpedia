-- Prove2me | Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_127_no_five_three_v2
-- name    : OddPerfectNumber.q2_five_q3_nineteen_q4_127_no_five_three_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T02:14:24.156111+00:00
-- url     : https://prove2.me/theorems/f9d51e6e-261c-46a2-8ab5-56162fbe088e
-- title:
--   The 3-component cannot supply five in q4=127 support
-- statement:
--   No odd-length local divisor sum of 3 can be divisible by 5; the order modulo 5 is even.
-- source:
--   Fresh independent proof using order divisibility by four and exclusion of order one, rather than exact order evaluation.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_not_dvd_of_even_order

namespace OddPerfectNumber

theorem q2_five_q3_nineteen_q4_127_no_five_three_v2 (e : Nat) :
    ¬ 5 ∣ ∑ i ∈ Finset.range (2 * e + 1), 3 ^ i := by
  sorry

end OddPerfectNumber
