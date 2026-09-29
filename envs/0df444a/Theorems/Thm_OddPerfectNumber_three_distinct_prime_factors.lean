-- Prove2me | Theorems.Thm_OddPerfectNumber_three_distinct_prime_factors
-- name    : OddPerfectNumber.three_distinct_prime_factors
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-07T20:15:43.841485+00:00
-- url     : https://prove2.me/theorems/fc51728a-a1a9-4560-afc9-f3ee64e76144
-- title:
--   An odd perfect number has at least three distinct prime divisors
-- statement:
--   **Classical lower bound.** If $N$ is odd and perfect, then $N$ has at least three distinct prime divisors: $\omega(N) \ge 3$, where $\omega$ counts distinct primes.
--
--   The argument is elementary and quantitative. If $N = \prod_{i} p_i^{a_i}$ then
--   $$\frac{\sigma(N)}{N} = \prod_i \frac{1 + p_i + \cdots + p_i^{a_i}}{p_i^{a_i}} < \prod_i \frac{p_i}{p_i - 1},$$
--   and for at most two distinct odd primes the right-hand side is bounded by $\tfrac{3}{2} \cdot \tfrac{5}{4} = \tfrac{15}{8} < 2$, so $\sigma(N) = 2N$ is impossible. This is the first step of the chain of lower bounds on $\omega(N)$ that culminates in the present record $\omega(N) \ge 10$.
--
--   Formalized with $\omega(N)$ as `N.primeFactors.card`.
-- source:
--   Classical; first stage of the Servais (1887) / Sylvester (1888) bounds. See https://en.wikipedia.org/wiki/Perfect_number#Odd_perfect_numbers .

import Mathlib

namespace OddPerfectNumber

theorem three_distinct_prime_factors (n : ℕ) (hn : Nat.Perfect n) (hodd : Odd n) :
    3 ≤ n.primeFactors.card := by
  sorry

end OddPerfectNumber
