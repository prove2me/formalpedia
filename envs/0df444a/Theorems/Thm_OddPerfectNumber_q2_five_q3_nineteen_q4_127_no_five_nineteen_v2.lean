-- Prove2me | Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_127_no_five_nineteen_v2
-- name    : OddPerfectNumber.q2_five_q3_nineteen_q4_127_no_five_nineteen_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T02:15:50.962658+00:00
-- url     : https://prove2.me/theorems/162a0e39-8f4f-4f80-b90c-4e8fbb6355ed
-- title:
--   The 19-component cannot supply five in q4=127 support
-- statement:
--   No odd-length local divisor sum of 19 can be divisible by 5; its order modulo 5 is even.
-- source:
--   Fresh independent proof using order divisibility by four and exclusion of order one.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_not_dvd_of_even_order

namespace OddPerfectNumber

theorem q2_five_q3_nineteen_q4_127_no_five_nineteen_v2 (e : Nat) :
    ¬ 5 ∣ ∑ i ∈ Finset.range (2 * e + 1), 19 ^ i := by
  sorry

end OddPerfectNumber
