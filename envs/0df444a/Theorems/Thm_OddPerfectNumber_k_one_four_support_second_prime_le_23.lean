-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_four_support_second_prime_le_23
-- name    : OddPerfectNumber.k_one_four_support_second_prime_le_23
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-16T18:55:45.989431+00:00
-- url     : https://prove2.me/theorems/db591aed-0bdb-4dfc-9fcc-b735a99b3d30
-- title:
--   The second support prime is at most 23
-- statement:
--   In the canonical odd perfect four-support equations, let q1<q2<q3<q4 be the ordered support primes. If q1=3, then the second support prime satisfies q2≤23.
-- source:
--   Source-faithful finite four-support abundance reduction: ordered support, multiplicative sigma factorization, the accepted geometric-sum cross inequality, and the canonical Euler relation force q2≤23.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_cross_lt_of_le
import Theorems.Thm_OddPerfectNumber_four_support_local_product_upper
import Theorems.Thm_OddPerfectNumber_four_support_factorization_expansion

namespace OddPerfectNumber

theorem k_one_four_support_second_prime_le_23 (p m d q1 q2 q3 q4 : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : m.primeFactors = {q1, q2, q3, q4})
    (hq1 : q1.Prime) (hq2 : q2.Prime) (hq3 : q3.Prime) (hq4 : q4.Prime)
    (horder : q1 < q2 ∧ q2 < q3 ∧ q3 < q4)
    (hq1eq : q1 = 3) : q2 ≤ 23 := by sorry

end OddPerfectNumber
