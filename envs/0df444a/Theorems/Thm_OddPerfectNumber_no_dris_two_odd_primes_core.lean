-- Prove2me | Theorems.Thm_OddPerfectNumber_no_dris_two_odd_primes_core
-- name    : OddPerfectNumber.no_dris_two_odd_primes_core
-- status  : Open
-- author  : @Gabewhigham
-- created : 2026-09-11T19:24:05.181711+00:00
-- url     : https://prove2.me/theorems/b846c97f-d24f-4976-ab4b-4e2081a2993e
-- title:
--   Dris index $s \\ge 2$ odd is impossible when $k+1$ has at least two odd prime factors
-- statement:
--   Let $p$ be a prime, let $k \ge 1$ be such that $k+1$ has at least two odd prime divisors, let $m$ be odd with $p \nmid m$, and let $s \ge 2$ be odd with $s \mid m^2$. Then the Dris relations
--
--   $$2m^2 = \sigma(p^k)\,s, \qquad \sigma(m^2) = p^k s$$
--
--   cannot both hold; equivalently, there is no odd perfect number $N = p^k m^2$ in Euler form whose Dris index $s = 2m^2/\sigma(p^k)$ is at least $2$, for such an exponent $k$.
--
--   This is the complement, in the special exponent $k$, of the case already isolated on the platform: when $k+1$ has **at most one** odd prime divisor, an index $s$ that is $1$ or an odd prime is ruled out by known results, and the remaining composite case is recorded as `OddPerfectNumber.no_dris_one_odd_prime_core`. The present statement is the residual core for all other exponents, that is, whenever $k+1$ carries two or more distinct odd primes; it generalises the exponent-specific core `OddPerfectNumber.no_dris_thirteen_core` from $k \ge 13$ with $p \equiv k \equiv 1 \pmod 4$ to an arbitrary prime $p$ and an arbitrary $k \ge 1$.
--
--   The difficulty is that the standard counting bound for the prime support of $m$, namely $\omega(m) \le \omega(s) + \Omega(s) + \#\{\text{odd primes of } k+1\}$, becomes weaker precisely when $k+1$ has several odd prime factors, so Sylvester's bound $\omega(N) \ge 5$ no longer yields a contradiction.
-- source:
--   J. A. B. Dris, The abundancy index of divisors of odd perfect numbers, Journal of Integer Sequences 15 (2012), Article 12.4.4, Section 2 (Dris parametrisation of the Euler equation).

import Mathlib
open Finset

namespace OddPerfectNumber

theorem no_dris_two_odd_primes_core (p k m s : Nat)
    (hp : p.Prime) (hk : k ≠ 0) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hk2 : 2 ≤ ((k + 1).primeFactors.erase 2).card)
    (hs2 : 2 ≤ s) (hs_not_even : ¬ Even s) (hs_dvd : s ∣ m ^ 2) :
    ¬ (2 * m ^ 2 = (∑ d ∈ (p ^ k).divisors, d) * s ∧
      (∑ d ∈ (m ^ 2).divisors, d) = p ^ k * s) := by
  sorry

end OddPerfectNumber
