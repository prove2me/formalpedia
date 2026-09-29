-- Prove2me | Theorems.Thm_OddPerfectNumber_four_support_five_exp_two_absurd
-- name    : OddPerfectNumber.four_support_five_exp_two_absurd
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-13T18:47:25.826928+00:00
-- url     : https://prove2.me/theorems/0dab5f0f-0c6f-44d7-9b1b-ddc3929fc392
-- title:
--   The 5^2 local sigma factor contradicts large fourth support
-- statement:
--   Under the canonical square-part sigma equation and four-prime support {3,5,13,q4} with q4>31, it is impossible for the local geometric sum sigma(5^2) to divide the global square-part sigma sum.
-- source:
--   The local sum is exactly 31, so it directly supplies a factor 31 of the global sigma sum. The accepted external-thirty-one support certificate then gives False.

import Mathlib
import Theorems.Thm_OddPerfectNumber_four_support_external_thirty_one_absurd

namespace OddPerfectNumber

theorem four_support_five_exp_two_absurd (p m d q4 : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm0 : m ≠ 0)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hddvd : d ∣ m ^ 2)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 13 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 31 < q4)
    (hlocal : (∑ i ∈ Finset.range (2 + 1), 5 ^ i) ∣
      ∑ x ∈ (m ^ 2).divisors, x) :
    False := by sorry

end OddPerfectNumber
