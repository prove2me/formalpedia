-- Prove2me | Theorems.Thm_OddPerfectNumber_q2_five_q3_twentynine_D27_nonexception_even_order_v2
-- name    : OddPerfectNumber.q2_five_q3_twentynine_D27_nonexception_even_order_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-16T14:25:09.144736+00:00
-- url     : https://prove2.me/theorems/258f5592-e587-4343-8e68-fb5da9b208fc
-- title:
--   D=27 q3=29 nonexceptional q4 orders are even v2
-- statement:
--   For every D=27 q3=29 fourth-prime candidate other than 47, 53, and 89, the multiplicative order modulo 53 is even.
-- source:
--   The q4=53 zero-residue case is intentionally excluded; for all remaining listed candidates, the order divisor bound and exact thirteenth-power computation force even order.

import Mathlib

namespace OddPerfectNumber

theorem q2_five_q3_twentynine_D27_nonexception_even_order_v2 (q4 : Nat) (hcases : q4 = 31 ∨ q4 = 37 ∨ q4 = 41 ∨ q4 = 43 ∨ q4 = 59 ∨ q4 = 61 ∨ q4 = 67 ∨ q4 = 71 ∨ q4 = 73 ∨ q4 = 79 ∨ q4 = 83) : Even (orderOf (q4 : ZMod 53)) := by
  sorry

end OddPerfectNumber
