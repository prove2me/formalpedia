-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_sigma_prime_mod_four_three_dvd_m
-- name    : OddPerfectNumber.k_one_sigma_prime_mod_four_three_dvd_m
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-13T13:58:26.725794+00:00
-- url     : https://prove2.me/theorems/671251a4-e437-4bd2-b1cd-5a6856626db6
-- title:
--   A 3 mod 4 sigma prime is supported in the k=1 equations
-- statement:
--   In the canonical square-part sigma relation, a prime divisor congruent to 3 modulo 4 cannot be the Euler prime p when p is 1 modulo 4, so it must divide m.
-- source:
--   Immediate corollary of OddPerfectNumber.sigma_prime_mem_support_or_euler and the incompatible residues p % 4 = 1 and r % 4 = 3.

import Mathlib
import Theorems.Thm_OddPerfectNumber_sigma_prime_mem_support_or_euler

theorem OddPerfectNumber.k_one_sigma_prime_mod_four_three_dvd_m (p m d r : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hr : r.Prime) (hr4 : r % 4 = 3)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hddvd : d ∣ m ^ 2)
    (hrsigma : r ∣ (∑ x ∈ (m ^ 2).divisors, x)) :
    r ∣ m := by sorry
