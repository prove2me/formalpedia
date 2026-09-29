-- Prove2me | Theorems.Thm_OddPerfectNumber_no_dris_index_odd_prime_of_one_odd_prime
-- name    : OddPerfectNumber.no_dris_index_odd_prime_of_one_odd_prime
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-11T08:57:42.153051+00:00
-- url     : https://prove2.me/theorems/2def7789-91ba-44fd-8906-7eba6e73bfdf
-- title:
--   No odd perfect number whose Dris index is an odd prime, when $k+1$ has at most one odd prime factor
-- statement:
--   **A prime Dris index is impossible when $k+1$ has at most one odd prime factor.**
--
--   In the Dris parametrisation of a hypothetical odd perfect number $N = p^k m^2$ (Euler form: $p$ the special prime, $m$ odd, $p \nmid m$), the *index* is the number $s$ with
--
--   $$2m^2 = \sigma(p^k)\, s, \qquad \sigma(m^2) = p^k s .$$
--
--   This statement rules out every **odd prime** index $s$, for every special exponent $k \ge 1$ whose successor $k+1$ has at most one odd prime divisor, i.e. $k+1 = 2^{a}q^{b}$ with $q$ prime. In particular it settles the indices $s = 3, 5, 7, 11, \dots$ for the special exponents $k = 1, 5, 9, 13$, where $k+1 = 2, 6, 10, 14$. (The index of an odd perfect number is always odd, since $\sigma(m^2)$ is odd for odd $m$; the case $s = 1$ is the theorem of Dandapat–Hunsucker–Pomerance.)
--
--   The hypothesis on $k+1$ is formalized as $\#\bigl(\mathrm{primeFactors}(k+1)\setminus\{2\}\bigr) \le 1$, and $\sigma$ is written as the sum over the divisor finset.
--
--   The proof rests on a counting bound for the prime support of $m$. Because $s$ is prime, $\sigma(m^2) = p^k s$ has only two prime divisors. For a prime $q \mid m$ with $q \ne s$ and $q^{a} \,\|\, m$, the divisor sum $\sigma(q^{2a})$ divides $p^ks$; if it is a pure power of $p$, then a lifting-the-exponent argument in the style of Dandapat–Hunsucker–Pomerance forces $q \mid k+1$, and otherwise $s \mid \sigma(q^{2a})$, which by $v_s(p^ks) = 1$ can happen for at most one prime $q$. Hence the primes of $m$ lie among $s$, the odd prime dividing $k+1$, and one exceptional prime, so $\omega(N) \le 4$ — contradicting Sylvester's bound $\omega(N) \ge 5$ for odd perfect numbers.
-- source:
--   Dris index parametrisation: J. A. B. Dris, The abundancy index of divisors of odd perfect numbers, Journal of Integer Sequences 15 (2012), Article 12.4.4, Section 2. Lifting-the-exponent technique: G. G. Dandapat, J. L. Hunsucker and C. Pomerance, Some new results on odd perfect numbers, Pacific J. Math. 57 (1975), 359-364, Theorem 1. Prime-count input: J. J. Sylvester (1888), omega(N) >= 5 for odd perfect N, as recorded on the Odd Perfect Number Conjecture mission (OddPerfectNumber.sylvester_five_distinct_prime_factors). Strengthening of OddPerfectNumber.no_dris_index_three_of_one_odd_prime from index 3 to an arbitrary odd prime index.

import Mathlib

namespace OddPerfectNumber

theorem no_dris_index_odd_prime_of_one_odd_prime (p k m s : Nat)
    (hp : p.Prime) (hs : s.Prime) (hs2 : s ≠ 2) (hk : k ≠ 0) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hk1 : ((k + 1).primeFactors.erase 2).card ≤ 1) :
    ¬ (2 * m ^ 2 = (∑ d ∈ (p ^ k).divisors, d) * s ∧
      (∑ d ∈ (m ^ 2).divisors, d) = p ^ k * s) := by
  sorry

end OddPerfectNumber
