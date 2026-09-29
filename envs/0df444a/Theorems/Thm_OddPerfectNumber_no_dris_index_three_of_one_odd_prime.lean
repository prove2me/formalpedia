-- Prove2me | Theorems.Thm_OddPerfectNumber_no_dris_index_three_of_one_odd_prime
-- name    : OddPerfectNumber.no_dris_index_three_of_one_odd_prime
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-11T08:41:28.251178+00:00
-- url     : https://prove2.me/theorems/a120a29c-5cda-42c4-b22a-a80d0a1ab7da
-- title:
--   No odd perfect number of Dris index $3$ when $k+1$ has at most one odd prime factor
-- statement:
--   **Dris index $3$ is impossible when $k+1$ has at most one odd prime factor.**
--
--   In the Dris parametrisation of a hypothetical odd perfect number $N = p^k m^2$ (Euler form: $p$ the special prime, $m$ odd, $p \nmid m$), the *index* is the number $s$ with
--
--   $$2m^2 = \sigma(p^k)\, s, \qquad \sigma(m^2) = p^k s .$$
--
--   This statement rules out the index $s = 3$ for every special exponent $k \ge 1$ whose successor $k+1$ has at most one odd prime divisor, i.e. $k + 1 = 2^{a} q^{b}$ for a prime $q$. In particular it settles the index-three case for the special exponents $k = 1, 5, 9, 13$, where $k+1 = 2, 6, 10, 14$.
--
--   The hypothesis on $k+1$ is formalized as $\#\bigl(\text{primeFactors}(k+1) \setminus \{2\}\bigr) \le 1$, and $\sigma$ is written as the sum over the divisor finset.
--
--   The proof combines two ingredients. Fixing $s = 3$ forces $3 \mid m$ and makes $\sigma(m^2) = 3p^k$ a number with only two prime divisors; a lifting-the-exponent argument in the style of Dandapat–Hunsucker–Pomerance then shows that a prime $q \mid m$ with $q \ne 3$ either divides $k+1$ or satisfies $3 \mid \sigma(q^{2a})$, where $q^{a} \,\|\, m$. Since $v_3(\sigma(m^2)) = 1$, at most one prime of the second kind exists, so $m$ has at most three distinct prime divisors and $N$ at most four — contradicting Sylvester's bound $\omega(N) \ge 5$ for odd perfect numbers.
-- source:
--   Dris index parametrisation: J. A. B. Dris, The abundancy index of divisors of odd perfect numbers, Journal of Integer Sequences 15 (2012), Article 12.4.4, Section 2. Lifting-the-exponent technique: G. G. Dandapat, J. L. Hunsucker and C. Pomerance, Some new results on odd perfect numbers, Pacific J. Math. 57 (1975), 359-364, Theorem 1. Prime-count input: J. J. Sylvester (1888), omega(N) >= 5 for odd perfect N, as recorded on the Odd Perfect Number Conjecture mission (OddPerfectNumber.sylvester_five_distinct_prime_factors).

import Mathlib

namespace OddPerfectNumber

theorem no_dris_index_three_of_one_odd_prime (p k m : Nat)
    (hp : p.Prime) (hk : k ≠ 0) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hk1 : ((k + 1).primeFactors.erase 2).card ≤ 1) :
    ¬ (2 * m ^ 2 = (∑ d ∈ (p ^ k).divisors, d) * 3 ∧
      (∑ d ∈ (m ^ 2).divisors, d) = p ^ k * 3) := by
  sorry

end OddPerfectNumber
