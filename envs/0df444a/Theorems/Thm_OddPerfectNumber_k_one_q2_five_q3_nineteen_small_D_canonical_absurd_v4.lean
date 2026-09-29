-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_small_D_canonical_absurd_v4
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_small_D_canonical_absurd_v4
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-15T03:09:47.366982+00:00
-- url     : https://prove2.me/theorems/48a80253-e924-4a1c-8708-16d608c92690
-- title:
--   Canonical q3=19 small-D contradiction v4
-- statement:
--   Under the accepted q3=19 exponent floors and exact q4 interval bounds, the accepted small-D survivor and prime enumerations reduce to the five exact tuples, which the canonical source bridge contradicts.
-- source:
--   Pure composition of accepted q3=19 small-D arithmetic and the changed canonical source bridge; no new number theory.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_small_D_survivors
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_small_D_q4_cases
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_small_D_canonical_source_bridge_v1

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_small_D_canonical_absurd_v4
    (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 19 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hDlt : D < 225) (hDodd : Odd D) (hp : p.Prime)
    (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime)
    (hq4gt : 19 < q4) (hDq : D < q4)
    (hDsupport : ∀ r, r.Prime → r ∣ D →
      r = 3 ∨ r = 5 ∨ r = 19 ∨ r = q4)
    (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e)
    (hDq4range :
      (D = 57 ∧ 580 ≤ q4 ∧ q4 ≤ 602) ∨
      (D = 75 ∧ 261 ≤ q4 ∧ q4 ≤ 264) ∨
      (D = 135 ∧ 146 ≤ q4 ∧ q4 ≤ 148)) :
    False := by
  sorry

end OddPerfectNumber
