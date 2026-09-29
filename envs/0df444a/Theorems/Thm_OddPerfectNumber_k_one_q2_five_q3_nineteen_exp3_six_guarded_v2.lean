-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp3_six_guarded_v2
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_exp3_six_guarded_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T09:57:44.703566+00:00
-- url     : https://prove2.me/theorems/027c2549-e118-42fd-a1f4-a9641e83bb61
-- title:
--   OddPerfectNumber.k_one_q2_five_q3_nineteen_exp3_six_guarded_v2
-- statement:
--   q19 full-3-exp=6 forces q4=1093 or p=1093 via sigma(3^6)=1093.
-- source:
--   q19 floor program; guarded six-disjunction.

import Mathlib
import Theorems.Thm_OddPerfectNumber_local_sigma_factor_dvd_global
import Theorems.Thm_OddPerfectNumber_four_support_sigma_prime_restricted

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_exp3_six_guarded_v2 (p m d q4 : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hddvd : d ∣ m ^ 2)
    (hm0 : m ≠ 0)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 19 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 19 < q4)
    (h3mem : 3 ∈ (m ^ 2).primeFactors)
    (h3exp : (m ^ 2).factorization 3 = 6) :
    q4 = 1093 ∨ p = 1093 := by
  sorry

end OddPerfectNumber
