-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_four_support_q2_ge_eleven_absurd_v2
-- name    : OddPerfectNumber.k_one_four_support_q2_ge_eleven_absurd_v2
-- status  : Open
-- author  : @WillR
-- created : 2026-09-15T23:54:09.133203+00:00
-- url     : https://prove2.me/theorems/3659c804-6869-40f9-9203-f59f2857effe
-- title:
--   Canonical four-support contradiction for q2 at least eleven v2
-- statement:
--   In the canonical k=1 four-support equations, if every support prime other than the smallest 3 is at least 11, the strict local geometric bounds contradict the Euler abundance lower bound.
-- source:
--   Changed membership adapter: supply the nonzero witness required by Nat.mem_primeFactors and close the smallest-prime cases by an explicit order bound.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_four_support_three_dvd
import Theorems.Thm_OddPerfectNumber_four_support_ordered
import Theorems.Thm_OddPerfectNumber_four_support_factorization_expansion
import Theorems.Thm_OddPerfectNumber_geom_sum_cross_lt_of_le

namespace OddPerfectNumber

theorem k_one_four_support_q2_ge_eleven_absurd_v2 (p m d : Nat) (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m) (hprod : m ^ 2 = ((p + 1) / 2) * d) (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d) (hcard : m.primeFactors.card = 4) (hsecond : ∀ q, q ∈ m.primeFactors → q = 3 ∨ 11 ≤ q) : False := by
  sorry

end OddPerfectNumber
