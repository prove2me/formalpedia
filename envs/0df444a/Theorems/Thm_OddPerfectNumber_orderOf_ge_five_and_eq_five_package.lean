-- Prove2me | Theorems.Thm_OddPerfectNumber_orderOf_ge_five_and_eq_five_package
-- name    : OddPerfectNumber.orderOf_ge_five_and_eq_five_package
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T16:38:53.341609+00:00
-- url     : https://prove2.me/theorems/d3a1614d-2ef3-4100-98e6-6dcfa4dd4c86
-- title:
--   Branch-I order package: orderOf q mod p is at least 5, and order 5 forces b = 1 and a = 4 mod 5
-- statement:
--   Branch I of the k = 1 endgame. Let p be a prime with p = 1 mod 4, let q be a prime dividing t = (p+1)/2, and let p divide the geometric sum 1 + q + ... + q^a with a = v_q(m^2). Write b = v_q(t) and h = orderOf (q : ZMod p). Then h >= 5. Moreover, if h = 5 then b = 1 and a = 4 mod 5. The proof composes two published results: the minimal-order Brent-Cohen-te Riele bound 3*b <= h - 1, obtained by feeding BCR the exponent h - 1 rather than a, and the cyclotomic bridge h | a + 1. Since b >= 1 this gives h >= 4, and since a = 2 * v_q(m) the exponent a + 1 is odd and every divisor of an odd number is odd, so h is odd; 4 <= h odd forces h >= 5. In the case h = 5 the inequality 3*b <= 4 with b >= 1 gives b = 1, and 5 | a + 1 gives a = 4 mod 5. No unique-source hypothesis, no quadratic-residue hypothesis, and no external Lemma-11 input is used. Published as an Open research child; no proof is asserted by this submission.
-- source:
--   Sections 14.2 and 14.3 of artifacts/K_ONE_Q_DVD_D_FRONTIER_AUDIT.md. Composes the Proved Branch-I ingredients OddPerfectNumber.three_mul_half_factorization_le_order_sub_one (node 03cb66de-783c-49a3-aaa3-4b6784a1d27b) and OddPerfectNumber.orderOf_q_mod_p_dvd_factorization_succ (node 7e4d3472-e085-4922-ae91-4b4be2b78eb9) with OddPerfectNumber.sq_factorization_two (node df481e23-de32-4479-8bda-3683cc273a8d).

import Mathlib

namespace OddPerfectNumber

theorem orderOf_ge_five_and_eq_five_package (p m q : Nat)
    (hp : p.Prime)
    (hp4 : p % 4 = 1)
    (hq : q.Prime)
    (hqdvd :
      p ∣ ∑ i ∈ Finset.range ((m ^ 2).factorization q + 1), q ^ i)
    (hqt : q ∣ (p + 1) / 2) :
    5 ≤ orderOf (q : ZMod p) ∧
      (orderOf (q : ZMod p) = 5 →
        ((p + 1) / 2).factorization q = 1 ∧
          (m ^ 2).factorization q % 5 = 4) := by
  sorry

end OddPerfectNumber
