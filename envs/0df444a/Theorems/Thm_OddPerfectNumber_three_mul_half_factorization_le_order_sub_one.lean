-- Prove2me | Theorems.Thm_OddPerfectNumber_three_mul_half_factorization_le_order_sub_one
-- name    : OddPerfectNumber.three_mul_half_factorization_le_order_sub_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T16:06:07.294293+00:00
-- url     : https://prove2.me/theorems/03cb66de-783c-49a3-aaa3-4b6784a1d27b
-- title:
--   Minimal-order BCR bound: three times the q-adic exponent of (p+1)/2 is at most orderOf q mod p minus one
-- statement:
--   Let p be a prime with p = 1 mod 4, and let q be a prime dividing t = (p+1)/2. Write b = v_q(t) for the exact q-adic exponent of t and h = ord_p(q) for the multiplicative order of q modulo p. Then 3*b <= h - 1. The proof replaces the naive application of the Brent-Cohen-te Riele valuation bound at exponent A = v_q(m^2), which only yields 3b <= v_q(m^2), by applying it at the minimal exponent A = h - 1: since p does not divide q - 1 and (q : ZMod p)^h = 1, the factorisation q^h - 1 = (q-1)(1 + q + ... + q^(h-1)) forces p | sigma(q^(h-1)). The hypothesis q | (p+1)/2 gives q^b || p+1 exactly because q is odd and p + 1 = 2*((p+1)/2). This theorem is published as an Open research child; no proof is asserted by this submission.
-- source:
--   Section 14.1 of artifacts/K_ONE_Q_DVD_D_FRONTIER_AUDIT.md, which derives 3*b <= h-1 from the Brent-Cohen-te Riele bound OddPerfectNumber.brent_cohen_te_riele_sigma_exp_bound (node a49802f6-c22d-49ff-be55-c93752c05608) instantiated at A = orderOf (q : ZMod p) - 1. Uses the geometric identity OddPerfectNumber.geom_mul_sub_one and standard multiplicative-order theory (orderOf_dvd_iff_pow_eq_one, ZMod.orderOf_dvd_card_sub_one).

import Mathlib

namespace OddPerfectNumber

theorem three_mul_half_factorization_le_order_sub_one (p q : Nat)
    (hp : p.Prime)
    (hp4 : p % 4 = 1)
    (hq : q.Prime)
    (hqt : q ∣ (p + 1) / 2) :
    3 * ((p + 1) / 2).factorization q ≤ orderOf (q : ZMod p) - 1 := by
  sorry

end OddPerfectNumber
