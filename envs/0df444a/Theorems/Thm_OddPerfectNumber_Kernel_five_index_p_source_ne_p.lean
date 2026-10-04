-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_five_index_p_source_ne_p
-- name    : OddPerfectNumber.Kernel.five_index_p_source_ne_p
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T17:08:50.626649+00:00
-- url     : https://prove2.me/theorems/9a44b3de-e5a7-443a-8563-2b7d5078b41e
-- title:
--   In the k=5 Dris situation the Euler prime p has a source prime different from p
-- statement:
--   Let p be a prime, k at least 1, and m a natural number with m squared nonzero. If p does not divide m and p to the k divides the divisor sum of m squared, then there is a natural number q that divides m squared, is not divisible by p, and such that p divides the geometric sum of the first factorization-exponent-plus-one powers of q.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem five_index_p_source_ne_p (p k m : Nat) (hp : p.Prime) (hk : 1 ≤ k)
    (hm2 : m ^ 2 != 0) (hpm : Not (Dvd.dvd p m))
    (hdvd : Dvd.dvd (p ^ k) (∑ x ∈ (m ^ 2).divisors, x)) :
    exists q : Nat, Dvd.dvd q (m ^ 2) /\ Not (Dvd.dvd p q) /\
      Dvd.dvd p (∑ i ∈ Finset.range ((m ^ 2).factorization q + 1), (q : Nat) ^ i) := by
  sorry

end OddPerfectNumber.Kernel
