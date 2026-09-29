-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_q4_59_no_five_source
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentythree_q4_59_no_five_source
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T19:23:40.141042+00:00
-- url     : https://prove2.me/theorems/437043df-d0fb-4b36-956d-ae5d2b5c9573
-- title:
--   The q3=23 q4=59 factor cannot supply five
-- statement:
--   For every even exponent e, the q4=59 local sigma factor of odd length e+1 is not divisible by 5.
-- source:
--   The residue 59=4 modulo 5 has multiplicative order 2, which is even; rewrite an even exponent as 2t and apply the accepted even-order geometric-sum obstruction.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_not_dvd_of_even_order

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentythree_q4_59_no_five_source (e : Nat)
    (heven : Even e) :
    ¬ 5 ∣ ∑ i ∈ Finset.range (e + 1), 59 ^ i := by
  sorry

end OddPerfectNumber
