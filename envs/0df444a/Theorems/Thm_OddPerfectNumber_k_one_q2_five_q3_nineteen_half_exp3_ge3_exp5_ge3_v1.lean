-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_half_exp3_ge3_exp5_ge3_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_half_exp3_ge3_exp5_ge3_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-17T10:10:36.988172+00:00
-- url     : https://prove2.me/theorems/d949a7d7-1432-4f27-bd52-0e20d5754a77
-- title:
--   Canonical q3=19 half exponents of 3 and 5 are at least three
-- statement:
--   Let p be prime with p congruent to 1 modulo 4, let m be odd with p not dividing m, and suppose m²=((p+1)/2)d and its divisor sum equals pd. Let q4>19 be prime, and suppose the prime support of m lies in {3,5,19,q4}. Write m²=3^(2a)5^(2b)19^(2c)q4^(2e), with positive half exponents a,b,c,e and with sigma equal to both the local geometric-sum product and the divisor sum. Assume the stated factorization coordinates at 3 and 5 equal 2a and 2b. Then
--
--   $$a \ge 3, \qquad b \ge 3.$$
--
--   Thus the full exponents of 3 and 5 are at least six. This is a structural lower-bound adapter for the q3=19 branch; it does not assert that the full exponent of 3 is at least eight or that of 19 is at least four.
-- source:
--   Interface strengthening of Prove2Me accepted q3=19 exponent-two/four exclusions (810c845e-49ec-421d-932a-fd0550bcd284, 24c19ee8-c5cd-4dc3-b9d3-0a92ee33a2ec, a3e47e33-9ca2-4675-939d-29e1939d5527), 31 role (451ed277-8e4e-4c2b-a212-c7a10f7ffce6), and q4=31 abundance (4655f38f-b1ce-4e75-9a1d-052f0f7684f1). Supplies missing floor provenance toward nineteen_absurd_v6 (032cf8a5-9aaf-4cad-99a9-121a9566c876), without importing that parent. Exact statements and decomposition directions inspected 2026-09-17.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp3_two_absurd
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp3_four_absurd
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp5_two_role
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp5_four_absurd
import Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_31_abundance_monotone

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_half_exp3_ge3_exp5_ge3_v1 (p m d q4 a b c e sigma : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 19 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 19 < q4)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 19 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hglobal : sigma = ∑ x ∈ (m ^ 2).divisors, x)
    (h3mem : 3 ∈ (m ^ 2).primeFactors)
    (h3exp : (m ^ 2).factorization 3 = 2*a)
    (h5mem : 5 ∈ (m ^ 2).primeFactors)
    (h5exp : (m ^ 2).factorization 5 = 2*b)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (he : 0 < e) :
    3 ≤ a ∧ 3 ≤ b := by sorry

end OddPerfectNumber
