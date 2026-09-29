-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_D_factor_support_form
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_D_factor_support_form
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-15T17:52:45.697437+00:00
-- url     : https://prove2.me/theorems/1f8f5af2-3a0d-410c-bbb9-f3fa76bb1b62
-- title:
--   Canonical q3=19 factor-support form for D
-- statement:
--   If the q2=5,q3=19 square factorization is accepted and D divides m^2, the canonical support restriction yields an exact four-prime factorization of D with exponents bounded by those of m^2.
-- source:
--   Use Nat.factorization, the accepted support restriction, and the factorization divisibility criterion; reconstruct D from its four possible prime coordinates and read the exponent bounds from D ∣ m^2.

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_D_factor_support_form (m a b c e D q4 : Nat) (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 19 ^ (2*c) * q4 ^ (2*e)) (hDdvd : D ∣ m ^ 2) (hDpos : 0 < D) (hq4prime : q4.Prime) (hq4gt : 19 < q4) (hDsupport : ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 19 ∨ r = q4) : ∃ i j k l, D = 3^i * 5^j * 19^k * q4^l ∧ i ≤ 2*a ∧ j ≤ 2*b ∧ k ≤ 2*c ∧ l ≤ 2*e := by sorry

end OddPerfectNumber
