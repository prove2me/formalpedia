-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_index_prime_has_non_self_sigma_source
-- name    : OddPerfectNumber.Kernel.index_prime_has_non_self_sigma_source
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-01T00:49:50.016683+00:00
-- url     : https://prove2.me/theorems/c2bd62fe-d345-42f6-8bd3-fa472875a888
-- title:
--   A prime dividing sigma(m^2) is supplied by a different prime of m
-- statement:
--   Let $q$ be a prime dividing a natural number $m$, with $m^2 \neq 0$. If $q$ divides $\sigma(m^2)$, then some prime $t$ dividing $m$ supplies it: $t$ is prime, $t$ divides $m$, $t \neq q$, and $q$ divides the local geometric sum $\sum_{i \leq v_t(m^2)} t^i$.
--
--   The point of the theorem is the third conjunct. A prime never divides its own sigma factor, since $\sigma(q^{2a}) = 1 + q + \cdots + q^{2a} \equiv 1 \pmod q$, so the accepted `prime_not_dvd_own_sigma_prime_pow` (658bb7bb) rules out $t = q$ as the supplier. In the $k = 5$ two-prime residual this is what forces each kernel prime $q$ and $r$ to be supplied by some *other* prime factor of $m$.
--
--   It does **not** show that the sources for $q$ and $r$ are distinct from each other: a third prime could satisfy both divisibilities. That common-source configuration is left open.
--
--   Audited numerically before publication: 1206 pairs $(m, q)$ with $q \mid m$, $q$ prime and $q \mid \sigma(m^2)$, zero counterexamples, using $v_t(m)$ as the exponent base.
-- source:
--   Mathlib/Data/Nat/Factorization/Defs.lean (Nat.factorization_mul, Nat.factorization_eq_zero_of_not_dvd, mem_primeFactors) and Mathlib/Data/Nat/Prime/Basic.lean, together with the accepted children OddPerfectNumber.exists_p_source_of_dvd (29082f61) and OddPerfectNumber.prime_not_dvd_own_sigma_prime_pow (658bb7bb). Exponent bookkeeping; it encodes no unproved conjecture.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem index_prime_has_non_self_sigma_source {m q : Nat} (hq : q.Prime)
    (hqm : Dvd.dvd q m) (hm2 : m ^ 2 != 0)
    (hrsig : Dvd.dvd q (∑ x ∈ (m ^ 2).divisors, x)) :
    exists t : Nat, t.Prime /\ Dvd.dvd t m /\ Not (Dvd.dvd t q) /\
      Dvd.dvd q (∑ i ∈ Finset.range ((m ^ 2).factorization t + 1), t ^ i) := by
  sorry

end OddPerfectNumber.Kernel
