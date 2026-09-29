-- Prove2me | Theorems.Thm_OddPerfectNumber_orderOf_q_mod_p_dvd_factorization_succ
-- name    : OddPerfectNumber.orderOf_q_mod_p_dvd_factorization_succ
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T16:27:11.058315+00:00
-- url     : https://prove2.me/theorems/7e4d3472-e085-4922-ae91-4b4be2b78eb9
-- title:
--   Multiplicative order of q mod p divides the q-adic exponent of m^2 plus one
-- statement:
--   Let a = v_q(m^2) = (m^2).factorization q and suppose p divides the geometric sum 1 + q + ... + q^a = sigma(q^a) (this is exactly the shape produced by the sigma-factor chain). Then the multiplicative order of q modulo p divides a + 1. The proof is the standard cyclotomic/geometric argument: q^(a+1) - 1 = (q - 1) * (1 + q + ... + q^a), so p | q^(a+1) - 1, hence (q : ZMod p)^(a+1) = 1, hence orderOf (q : ZMod p) | a + 1. Primality of p and p != q are NOT needed: the statement holds for every p and every q with 1 <= q. Published as an Open research child; no proof is asserted by this submission.
-- source:
--   Section 5.2 / C3 of artifacts/K_ONE_Q_DVD_D_FRONTIER_AUDIT.md. Uses the Proved node OddPerfectNumber.geom_mul_sub_one (069159f8-59c6-4023-af9d-5ad6dabcdf1b) for the telescoping identity, the Proved node OddPerfectNumber.zmod_pow_eq_one_iff (890d5806-d6f3-4d4c-8ec3-42d96f9b4165) as the Nat/ZMod bridge, and Mathlib's orderOf_dvd_of_pow_eq_one.

import Mathlib

namespace OddPerfectNumber

theorem orderOf_q_mod_p_dvd_factorization_succ (p m q : Nat)
    (hq : 1 ≤ q)
    (hqdvd :
      p ∣ ∑ i ∈ Finset.range ((m ^ 2).factorization q + 1), q ^ i) :
    orderOf (q : ZMod p) ∣ (m ^ 2).factorization q + 1 := by
  sorry

end OddPerfectNumber
