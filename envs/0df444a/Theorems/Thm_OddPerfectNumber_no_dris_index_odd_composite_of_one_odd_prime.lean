-- Prove2me | Theorems.Thm_OddPerfectNumber_no_dris_index_odd_composite_of_one_odd_prime
-- name    : OddPerfectNumber.no_dris_index_odd_composite_of_one_odd_prime
-- status  : Open
-- author  : @Gabewhigham
-- created : 2026-09-11T09:03:16.774823+00:00
-- url     : https://prove2.me/theorems/9fcfa415-608e-4049-8ff2-d0f93460c709
-- title:
--   No odd perfect number whose Dris index is odd and composite, when $k+1$ has at most one odd prime factor
-- statement:
--   **Composite Dris index, at an exponent whose successor has one odd prime factor.**
--
--   In the Dris parametrisation of a hypothetical odd perfect number $N = p^k m^2$ (Euler form: $p$ the special prime, $m$ odd, $p \nmid m$), the *index* is the number $s$ with
--
--   $$2m^2 = \sigma(p^k)\, s, \qquad \sigma(m^2) = p^k s .$$
--
--   The index is necessarily odd. This statement asserts that no **odd composite** index $s \ge 2$ occurs, for a special exponent $k \ge 1$ whose successor has at most one odd prime divisor, i.e. $k+1 = 2^{a}q^{b}$ with $q$ prime; the hypothesis is formalized as $\#\bigl(\mathrm{primeFactors}(k+1)\setminus\{2\}\bigr) \le 1$.
--
--   This is the residual index range for such exponents. The index $s = 1$ is excluded by the theorem of Dandapat–Hunsucker–Pomerance, and every odd prime index is excluded by `OddPerfectNumber.no_dris_index_odd_prime_of_one_odd_prime`; together with the present statement these cover all indices, so proving it settles the Dris problem for the special exponents $k = 1, 5, 9, 13$ (where $k+1 = 2, 6, 10, 14$).
--
--   The obstruction used for a prime index does not extend as it stands. For prime $s$ the divisor sum $\sigma(m^2) = p^ks$ has only two prime divisors, which bounds the prime support of $m$ by three ($s$ itself, the odd prime dividing $k+1$, and one exceptional prime whose divisor sum absorbs the factor $s$), contradicting Sylvester's bound $\omega(N) \ge 5$. For composite $s$ the same counting gives only $\omega(m) \le \omega(s) + \Omega(s) + 1$, which is no longer smaller than $4$.
-- source:
--   J. A. B. Dris, The abundancy index of divisors of odd perfect numbers, Journal of Integer Sequences 15 (2012), Article 12.4.4, Section 2 (Dris parametrisation of the Euler equation); residual index range on the Odd Perfect Number Conjecture mission after the index-one case (G. G. Dandapat, J. L. Hunsucker and C. Pomerance, Some new results on odd perfect numbers, Pacific J. Math. 57 (1975), 359-364, Theorem 1) and the prime-index case (OddPerfectNumber.no_dris_index_odd_prime_of_one_odd_prime).

import Mathlib

namespace OddPerfectNumber

theorem no_dris_index_odd_composite_of_one_odd_prime (p k m s : Nat)
    (hp : p.Prime) (hk : k ≠ 0) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hk1 : ((k + 1).primeFactors.erase 2).card ≤ 1)
    (hs2 : 2 ≤ s) (hs_not_even : ¬ Even s) (hs_not_prime : ¬ s.Prime) :
    ¬ (2 * m ^ 2 = (∑ d ∈ (p ^ k).divisors, d) * s ∧
      (∑ d ∈ (m ^ 2).divisors, d) = p ^ k * s) := by
  sorry

end OddPerfectNumber
