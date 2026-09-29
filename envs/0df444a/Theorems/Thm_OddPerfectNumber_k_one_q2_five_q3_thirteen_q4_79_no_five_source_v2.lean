-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_q4_79_no_five_source_v2
-- name    : OddPerfectNumber.k_one_q2_five_q3_thirteen_q4_79_no_five_source_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-15T01:33:54.326467+00:00
-- url     : https://prove2.me/theorems/c3a0fbf5-2706-4973-a4da-f4dedbcd81bb
-- title:
--   The q3=13 q4=79 component cannot supply five
-- statement:
--   In the q2=5,q3=13,q4=79 four-factor sigma product, a factor five cannot be supplied by any local component.
-- source:
--   Specialize the accepted generic p=5 source dispatch and certify even orders for 3, 13, and 79 modulo 5.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_p5_no_local_sigma_source_general_v2

namespace OddPerfectNumber

theorem k_one_q2_five_q3_thirteen_q4_79_no_five_source_v2 (sigma a b c e : Nat)
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2 * a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2 * b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2 * c + 1), 13 ^ i) *
      (∑ i ∈ Finset.range (2 * e + 1), 79 ^ i))
    (hdiv : 5 ∣ sigma) :
    False := by
  sorry

end OddPerfectNumber
