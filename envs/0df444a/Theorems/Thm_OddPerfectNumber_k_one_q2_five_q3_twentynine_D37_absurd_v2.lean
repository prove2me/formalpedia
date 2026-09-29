-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_D37_absurd_v2
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentynine_D37_absurd_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-15T08:26:03.786472+00:00
-- url     : https://prove2.me/theorems/012ebd2c-f594-4e60-b8dd-0afbd6e1d1dd
-- title:
--   Reduced canonical q3=29 D=37 contradiction v2
-- statement:
--   In the exact q3=29,D=37,p=73,q4=37 arm, the accepted source/order chain forces an external 127 divisor of sigma(m^2), contradicting four-prime support.
-- source:
--   Specialize q4=37 before applying the accepted source children, lift the local 127 divisor to the canonical sigma(m^2) via hglobal, and consume the accepted external-prime contradiction.

import Mathlib
import Theorems.Thm_OddPerfectNumber_q2_five_q3_twentynine_D37_source_forces_37
import Theorems.Thm_OddPerfectNumber_q2_five_q3_twentynine_D37_source_length
import Theorems.Thm_OddPerfectNumber_q2_five_q3_twentynine_D37_local_127_of_length9
import Theorems.Thm_OddPerfectNumber_q2_five_q3_twentynine_D37_external_127_sigma_lift
import Theorems.Thm_OddPerfectNumber_q2_five_q3_twentynine_D37_external_127_absurd

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentynine_D37_absurd_v2 (m d D p q4 sigma a b c e : Nat) (hsigma : sigma = (∑ i ∈ Finset.range (2 * a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2 * b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2 * c + 1), 29 ^ i) * (∑ i ∈ Finset.range (2 * e + 1), q4 ^ i)) (hrel : D * sigma = p * m ^ 2) (hD : D = 37) (hp_eq : p = 2 * D - 1) (hp : p.Prime) (hp4 : p % 4 = 1) (hm0 : m ≠ 0) (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d) (hglobal : sigma = ∑ x ∈ (m ^ 2).divisors, x) (hddvd : d ∣ m ^ 2) (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 29 ∨ x = q4) (hq4prime : q4.Prime) (hq4eq : q4 = 37) (haEven : Even a) (hbEven : Even b) (hcEven : Even c) (heEven : Even e) : False := by
  sorry

end OddPerfectNumber
