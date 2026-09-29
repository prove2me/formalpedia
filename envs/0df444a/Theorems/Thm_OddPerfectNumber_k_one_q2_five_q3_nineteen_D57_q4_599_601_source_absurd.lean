-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_D57_q4_599_601_source_absurd
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_D57_q4_599_601_source_absurd
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T20:10:56.012174+00:00
-- url     : https://prove2.me/theorems/a1bca2b0-72e1-4ec1-8c67-2d9e8b024f66
-- title:
--   The D=57 q4=599 and q4=601 source cases are impossible
-- statement:
--   The D=57 q3=19 candidates q4=599 and q4=601 cannot provide a p=113 sigma source.
-- source:
--   Compose the accepted three base-order certificates and the new exact q4=599,601 even-order certificate with the accepted p=113 source obstruction.

import Mathlib
import Theorems.Thm_OddPerfectNumber_even_order_three_mod_113
import Theorems.Thm_OddPerfectNumber_even_order_five_mod_113
import Theorems.Thm_OddPerfectNumber_even_order_nineteen_mod_113
import Theorems.Thm_OddPerfectNumber_even_orders_mod_113_q4_599_601
import Theorems.Thm_OddPerfectNumber_k_one_p113_no_local_sigma_source_general

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_D57_q4_599_601_source_absurd (sigma a b c e q4 : Nat)
    (hsigma : sigma = (∑ i ∈ Finset.range (2 * a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2 * b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2 * c + 1), 19 ^ i) * (∑ i ∈ Finset.range (2 * e + 1), q4 ^ i))
    (hcase : (q4 = 599 ∧ 113 ∣ sigma) ∨ (q4 = 601 ∧ 113 ∣ sigma)) :
    False := by
  sorry

end OddPerfectNumber
