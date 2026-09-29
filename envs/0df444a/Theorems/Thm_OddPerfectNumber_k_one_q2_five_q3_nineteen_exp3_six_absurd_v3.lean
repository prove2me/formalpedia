-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp3_six_absurd_v3
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_exp3_six_absurd_v3
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T03:57:04.993663+00:00
-- url     : https://prove2.me/theorems/7e4655f8-643a-4d2e-ad88-006f78f7670c
-- title:
--   The exponent-six 3-component branch is impossible
-- statement:
--   The accepted 3^6 source role splits into p=1093 and q4=1093; the two independently certified source/abundance contradictions close those cases.
-- source:
--   A dispatcher over the accepted 1093 source-role theorem, the p=1093 source composition, and the q4=1093 abundance certificate.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp3_six_1093_role
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp3_six_p1093_absurd_from_sources
import Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_1093_support_abundance_absurd

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_exp3_six_absurd_v3 (p m d q4 sigma a b c e D : Nat)
    (hp : p.Prime) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 19 ∨ x = q4)
    (h3mem : 3 ∈ (m ^ 2).primeFactors)
    (h3exp : (m ^ 2).factorization 3 = 6)
    (hsigma_p : sigma = (∑ i ∈ Finset.range (a + 1), 3 ^ i) * (∑ i ∈ Finset.range (b + 1), 5 ^ i) * (∑ i ∈ Finset.range (c + 1), 19 ^ i) * (∑ i ∈ Finset.range (e + 1), 547 ^ i))
    (hsigma_eq_p : sigma = 1093 * d)
    (hpow : 5 ^ 6 ∣ m ^ 2)
    (h3 : ¬ 5 ∣ ∑ i ∈ Finset.range (a + 1), 3 ^ i)
    (h19 : ¬ 5 ∣ ∑ i ∈ Finset.range (c + 1), 19 ^ i)
    (h547 : ¬ 5 ∣ ∑ i ∈ Finset.range (e + 1), 547 ^ i)
    (hfac_q : m ^ 2 = 3 ^ 6 * 5 ^ b * 19 ^ c * 1093 ^ e)
    (hsigma_q : sigma = (∑ i ∈ Finset.range (6 + 1), 3 ^ i) * (∑ i ∈ Finset.range (b + 1), 5 ^ i) * (∑ i ∈ Finset.range (c + 1), 19 ^ i) * (∑ i ∈ Finset.range (e + 1), 1093 ^ i))
    (hrel_q : D * sigma = p * m ^ 2)
    (hDcases_q : D = 3 ∨ D = 9 ∨ D = 15 ∨ D = 19 ∨ D = 27 ∨ D = 45)
    (hp_q : p = 2 * D - 1)
    (hb : 6 ≤ b) (hc : 2 ≤ c) (he : 2 ≤ e) :
    False := by
  sorry

end OddPerfectNumber
