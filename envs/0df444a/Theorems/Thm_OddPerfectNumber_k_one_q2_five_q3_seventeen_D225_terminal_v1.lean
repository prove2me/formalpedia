-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_seventeen_D225_terminal_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_seventeen_D225_terminal_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T12:04:43.168231+00:00
-- url     : https://prove2.me/theorems/354fa9d5-24d0-404e-93f5-5f1955c14097
-- title:
--   q17 D225 even-order terminal
-- statement:
--   Under q17 canonical factorisation with D=225 (p=449) and q4 one of the six enumerated primes, all four local sigma lengths are odd while every support base has even order mod 449: impossible.
-- source:
--   D225 terminal consuming the six-case enumeration + nine proved even-order certs + generic even/odd lemma.

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_seventeen_D225_terminal_v1 (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 17 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 17 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hp_eq : p = 2 * D - 1) (hp : p.Prime)
    (hq4 : q4.Prime)
    (hD : D = 225)
    (hcase : q4 = 103 ∨ q4 = 137 ∨ q4 = 239 ∨ q4 = 307 ∨ q4 = 409 ∨ q4 = 443) :
    False := by sorry

end OddPerfectNumber
