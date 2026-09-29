-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_seventeen_D289_terminal_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_seventeen_D289_terminal_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T12:09:22.339567+00:00
-- url     : https://prove2.me/theorems/63bf943f-925c-4bad-b359-0fdb60e1714f
-- title:
--   q17 D289 even-order terminal
-- statement:
--   Under q17 canonical factorisation with D=289 (p=577) and q4 one of the nine enumerated primes, all four local sigma lengths are odd while every support base has even order mod 577: impossible.
-- source:
--   D289 terminal consuming the nine-case enumeration + twelve proved even-order certs + generic even/odd lemma.

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_seventeen_D289_terminal_v1 (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 17 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 17 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hp_eq : p = 2 * D - 1) (hp : p.Prime)
    (hq4 : q4.Prime)
    (hD : D = 289)
    (hcase : q4 = 31 ∨ q4 = 61 ∨ q4 = 151 ∨ q4 = 181 ∨ q4 = 211 ∨ q4 = 241 ∨ q4 = 271 ∨ q4 = 331 ∨ q4 = 421) :
    False := by sorry

end OddPerfectNumber
