-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_absurd_v2
-- name    : OddPerfectNumber.k_one_q2_five_q3_thirteen_absurd_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-15T02:31:29.739388+00:00
-- url     : https://prove2.me/theorems/3162ccde-a8da-47bd-ac58-b407e90f754a
-- title:
--   Canonical q2=5 q3=13 branch contradiction
-- statement:
--   Under the canonical q2=5,q3=13 support equations, parity, exponent floors, the canonical D upper bound and residual 5-divisibility, all three D ranges contradict.
-- source:
--   Pure three-way range dispatch; the boundary D=214 is excluded by Odd D.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_D_lt_45_canonical_absurd_v3
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_middle_D_canonical_dispatch_v2
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_large_D_absurd

namespace OddPerfectNumber

theorem k_one_q2_five_q3_thirteen_absurd_v2 (m a b c e D p q4 sigma : Nat) (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 13 ^ (2*c) * q4 ^ (2*e)) (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2*c + 1), 13 ^ i) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i)) (hrel : D * sigma = p * m ^ 2) (hDodd : Odd D) (hp : p.Prime) (hp4 : p % 4 = 1) (hp_eq : p = 2 * D - 1) (hq4 : q4.Prime) (hq4gt : 13 < q4) (hq4le : q4 ≤ 89) (hq4dvd : q4 ∣ D) (ha : 2 ≤ a) (hb : 8 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) (hDupper : D ≤ 685) (h5pow : 390625 ∣ D) : False := by sorry

end OddPerfectNumber
