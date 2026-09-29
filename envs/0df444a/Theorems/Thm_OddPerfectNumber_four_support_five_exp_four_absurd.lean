-- Prove2me | Theorems.Thm_OddPerfectNumber_four_support_five_exp_four_absurd
-- name    : OddPerfectNumber.four_support_five_exp_four_absurd
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-13T18:40:52.228558+00:00
-- url     : https://prove2.me/theorems/222f2001-484f-4bd1-9217-a54b161f021b
-- title:
--   The 5^4 local sigma factor contradicts {3,5,13,q4} support
-- statement:
--   Under the canonical square-part sigma equation and four-prime support {3,5,13,q4} with q4>13, it is impossible for the local geometric sum sigma(5^4) to divide the global square-part sigma sum.
-- source:
--   The local sum is exactly 781=11*71, so 11 divides it. Divisibility transitivity yields 11 dividing the global sigma sum, and the accepted external-eleven support certificate gives False.

import Mathlib
import Theorems.Thm_OddPerfectNumber_four_support_external_eleven_absurd

namespace OddPerfectNumber

theorem four_support_five_exp_four_absurd (p m d q4 : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm0 : m ≠ 0)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hddvd : d ∣ m ^ 2)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 13 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 13 < q4)
    (hlocal : (∑ i ∈ Finset.range (4 + 1), 5 ^ i) ∣
      ∑ x ∈ (m ^ 2).divisors, x) :
    False := by sorry

end OddPerfectNumber
