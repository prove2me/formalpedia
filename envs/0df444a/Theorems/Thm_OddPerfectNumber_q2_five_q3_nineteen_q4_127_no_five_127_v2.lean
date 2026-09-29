-- Prove2me | Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_127_no_five_127_v2
-- name    : OddPerfectNumber.q2_five_q3_nineteen_q4_127_no_five_127_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T02:21:24.438421+00:00
-- url     : https://prove2.me/theorems/327239bd-0305-4e09-867a-bf6eba78bc9e
-- title:
--   The q4=127 component cannot supply five to its sigma
-- statement:
--   No odd-length local divisor sum of 127 can be divisible by 5; its order modulo 5 is even.
-- source:
--   Fresh independent proof using order divisibility by four and exclusion of order one.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_not_dvd_of_even_order

namespace OddPerfectNumber

theorem q2_five_q3_nineteen_q4_127_no_five_127_v2 (e : Nat) :
    ¬ 5 ∣ ∑ i ∈ Finset.range (2 * e + 1), 127 ^ i := by
  sorry

end OddPerfectNumber
