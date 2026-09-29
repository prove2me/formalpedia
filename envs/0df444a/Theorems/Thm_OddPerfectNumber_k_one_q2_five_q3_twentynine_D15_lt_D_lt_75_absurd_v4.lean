-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_D15_lt_D_lt_75_absurd_v4
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentynine_D15_lt_D_lt_75_absurd_v4
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T09:25:45.816865+00:00
-- url     : https://prove2.me/theorems/4f886a83-fa15-4767-94ea-3d6ae7138aec
-- title:
--   OddPerfectNumber.k_one_q2_five_q3_twentynine_D15_lt_D_lt_75_absurd_v4
-- statement:
--   Small-D dispatch over D in {27,31,37,45} with canonical half-exponent floors.
-- source:
--   Small-D assembler.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_small_D_cases_canonical_v7
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_D27_absurd_v2
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_D31_absurd_v2
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_D37_absurd_v3
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_D45_canonical_absurd_v3

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentynine_D15_lt_D_lt_75_absurd_v4 (m d D p q4 sigma a b c e : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hDgt : 15 < D) (hDlt : D < 75) (hDodd : Odd D)
    (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hp4 : p % 4 = 1)
    (hq4prime : q4.Prime) (hq4gt : 29 < q4)
    (hDsupport : ∀ r, r.Prime → r ∣ D →
      r = 3 ∨ r = 5 ∨ r = 29 ∨ r = q4)
    (hm0 : m ≠ 0)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hglobal : sigma = ∑ x ∈ (m ^ 2).divisors, x)
    (hddvd : d ∣ m ^ 2)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 29 ∨ x = q4)
    (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) : False := by
  sorry

end OddPerfectNumber
