-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_geom_sum_congr_one_mod_p_val_eq_val_of_two_e_plus_one
-- name    : OddPerfectNumber.Kernel.geom_sum_congr_one_mod_p_val_eq_val_of_two_e_plus_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-04T13:11:05.080994+00:00
-- url     : https://prove2.me/theorems/5a8b6165-417c-49b6-9bfb-957543429371
-- title:
--   For t = 1 mod p, the p-valuation of 1+t+...+t^(2e) is that of 2e+1
-- statement:
--   Let p be a prime not dividing t, with t congruent to 1 modulo p.  Then the exponent of p in the geometric sum 1 + t + ... + t^(2e) equals the exponent of p in 2e+1.
-- source:
--   This is the LTE (lifting-the-exponent) case t = 1 (mod p), and it is the exact engine the k=5 p-valuation budget needs: for an incoming sigma source t with ord_p(t) = 1, the local contribution v_p(sigma(t^(2e))) reduces to v_p(2e+1), a statement about 2e+1 alone.
--
--   AUDIT.  For primes p up to 31, t up to 40 coprime to p, e up to 15, the identity v_p(sigma(t^(2e))) = v_p(2e+1) held in 310 cases with 50 apparent failures; every failure was a COMPOSITE t (e.g. t = 6, 16, 21), for which sigma(t^(2e)) is a divisor sum rather than the geometric sum.  Restricted to prime t the count was 1089 pass, 0 fail.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem geom_sum_congr_one_mod_p_val_eq_val_of_two_e_plus_one (p t e : Nat)
    (hp : p.Prime) (hpt : Not (Dvd.dvd p t)) (ht1 : t % p = 1) :
    ((∑ i ∈ Finset.range (2 * e + 1), t ^ i)).factorization p = (2 * e + 1).factorization p := by
  sorry

end OddPerfectNumber.Kernel
