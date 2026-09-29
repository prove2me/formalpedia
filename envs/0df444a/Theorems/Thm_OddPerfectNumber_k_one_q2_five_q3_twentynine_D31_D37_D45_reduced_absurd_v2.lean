-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_D31_D37_D45_reduced_absurd_v2
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentynine_D31_D37_D45_reduced_absurd_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-15T23:15:45.287165+00:00
-- url     : https://prove2.me/theorems/7c77ad64-f0e0-4015-8c90-bd6807994996
-- title:
--   q3=29 exact D31 D37 D45 reduced dispatch v2
-- statement:
--   The exact q3=29 D=31, D=37, and D=45 reduced survivors are contradictory; D=27 remains outside this dispatcher.
-- source:
--   Clean replacement for the under-specified historical dispatcher: split D, derive q4=31 or 37 from support-divisor arithmetic, and dispatch D=45 through the accepted q4=31∨41 terminal.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_D31_absurd_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_D37_canonical_absurd_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_D45_q4_cases_absurd

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentynine_D31_D37_D45_reduced_absurd_v2 (m d D p q4 sigma a b c e : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2) (hDcases : D = 31 ∨ D = 37 ∨ D = 45)
    (hp_eq : p = 2 * D - 1) (hp : p.Prime) (hp4 : p % 4 = 1) (hm0 : m ≠ 0)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hglobal : sigma = ∑ x ∈ (m ^ 2).divisors, x) (hddvd : d ∣ m ^ 2)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 29 ∨ x = q4)
    (hDsupport : ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 29 ∨ r = q4)
    (hq4prime : q4.Prime) (haEven : Even a) (hbEven : Even b)
    (hcEven : Even c) (heEven : Even e)
    (hD45q4 : D = 45 → q4 = 31 ∨ q4 = 41)
    (ha : 8 ≤ a) (hb : 6 ≤ b) (hc : 4 ≤ c) (he : 2 ≤ e) :
    False := by
  sorry

end OddPerfectNumber
