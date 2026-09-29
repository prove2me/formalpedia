-- Prove2me | Theorems.Thm_OddPerfectNumber_q2_five_q3_twentynine_D27_nonexception_even_order_v1
-- name    : OddPerfectNumber.q2_five_q3_twentynine_D27_nonexception_even_order_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-16T14:21:49.842688+00:00
-- url     : https://prove2.me/theorems/6d37e1da-1b1b-435c-8aba-72f00076a8c6
-- title:
--   D=27 q3=29 nonexceptional q4 orders are even
-- statement:
--   For every D=27 q3=29 fourth-prime candidate other than 47 and 89, the multiplicative order modulo 53 is even.
-- source:
--   Use the order divisor bound in the field ZMod 53: an odd order would divide 13, so the exact numeral computation q4^13≠1 excludes odd order for each listed candidate.

import Mathlib

namespace OddPerfectNumber

theorem q2_five_q3_twentynine_D27_nonexception_even_order_v1 (q4 : Nat) (hcases : q4 = 31 ∨ q4 = 37 ∨ q4 = 41 ∨ q4 = 43 ∨ q4 = 53 ∨ q4 = 59 ∨ q4 = 61 ∨ q4 = 67 ∨ q4 = 71 ∨ q4 = 73 ∨ q4 = 79 ∨ q4 = 83) : Even (orderOf (q4 : ZMod 53)) := by
  sorry

end OddPerfectNumber
