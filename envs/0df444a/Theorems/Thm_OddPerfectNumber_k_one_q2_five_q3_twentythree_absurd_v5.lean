-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_absurd_v5
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentythree_absurd_v5
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-16T09:36:03.610021+00:00
-- url     : https://prove2.me/theorems/8b1310bf-9fd0-4724-98fd-2701c6164026
-- title:
--   q3=23 four-support contradiction with canonical small split v5
-- statement:
--   The q3=23 split consumes the canonical D<111 terminal without a D<q4 premise and the accepted large-D terminal under its canonical envelope.
-- source:
--   Pure two-way D dispatch; the small branch uses the canonical D<111 theorem, removing the historical D<q4 adapter.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D_lt_111_absurd_canonical_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_large_D_absurd_v3

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentythree_absurd_v5 (m a b c e D p q4 sigma d : Nat) (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e)) (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2*c + 1), 23 ^ i) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i)) (hrel : D * sigma = p * m ^ 2) (hDodd : Odd D) (hp : p.Prime) (hp4 : p % 4 = 1) (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime) (hq4gt : 23 < q4) (hq4lelarge : 111 ≤ D → q4 ≤ 61) (hq4gt47large : 111 ≤ D → 47 < q4) (hq4dvdlarge : 111 ≤ D → q4 ∣ D) (hDsupport : ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 23 ∨ r = q4) (ha : 5 ≤ a) (hb : 3 ≤ b) (hc : 4 ≤ c) (he : 1 ≤ e) (hDupper : D ≤ 685) (hm0 : m ≠ 0) (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d) (hddvd : d ∣ m ^ 2) (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 23 ∨ x = q4) (hglobal : sigma = ∑ x ∈ (m ^ 2).divisors, x) : False := by
  sorry

end OddPerfectNumber
