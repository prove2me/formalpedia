-- Prove2me | Theorems.Thm_OddPerfectNumber_q2_five_q3_twentynine_D27_nonexception_absurd_v2
-- name    : OddPerfectNumber.q2_five_q3_twentynine_D27_nonexception_absurd_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-16T14:37:30.1808+00:00
-- url     : https://prove2.me/theorems/4f113d38-b230-47ac-9f55-cc6aa180ce76
-- title:
--   D=27 q3=29 nonexceptional q4 contradiction v2
-- statement:
--   In the q3=29 D=27 branch, every listed fourth prime other than 47, 53, and 89 has even order modulo 53, contradicting the accepted source bridge.
-- source:
--   Apply the accepted D=27 source bridge and the v2 finite even-order certificate to the listed nonexceptional fourth-prime candidates.

import Mathlib
import Theorems.Thm_OddPerfectNumber_q2_five_q3_twentynine_D27_source_bridge_v1
import Theorems.Thm_OddPerfectNumber_q2_five_q3_twentynine_D27_nonexception_even_order_v2
import Theorems.Thm_OddPerfectNumber_geom_sum_not_dvd_of_even_order

namespace OddPerfectNumber

theorem q2_five_q3_twentynine_D27_nonexception_absurd_v2 (D p sigma m a b c e q4 : Nat) (hrel : D * sigma = p * m ^ 2) (hD : D = 27) (hp_eq : p = 2 * D - 1) (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i)) (hcases : q4 = 31 ∨ q4 = 37 ∨ q4 = 41 ∨ q4 = 43 ∨ q4 = 59 ∨ q4 = 61 ∨ q4 = 67 ∨ q4 = 71 ∨ q4 = 73 ∨ q4 = 79 ∨ q4 = 83) : False := by
  sorry

end OddPerfectNumber
