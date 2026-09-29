-- Prove2me | Theorems.Thm_OddPerfectNumber_no_dris_thirteen_s_ge_two_two_odd_primes
-- name    : OddPerfectNumber.no_dris_thirteen_s_ge_two_two_odd_primes
-- status  : Open
-- author  : @Gabewhigham
-- created : 2026-09-11T09:08:38.252012+00:00
-- url     : https://prove2.me/theorems/165c979b-f64d-4c4b-83ea-354d3f9d05df
-- title:
--   Odd Dris index at $k \ge 13$ when $k+1$ has at least two odd prime factors
-- statement:
--   Let $p$ be an odd prime with $p \equiv 1 \pmod 4$, let $k \equiv 1 \pmod 4$ with $k \ge 13$, let $m$ be odd with $p \nmid m$, and let $s \ge 2$ be odd. Assume moreover that $k+1$ has **at least two** odd prime divisors, i.e.
--
--   $$\#\bigl(\mathrm{primeFactors}(k+1)\setminus\{2\}\bigr) \ \ge\ 2 .$$
--
--   Then the two Dris relations
--
--   $$2m^2 = \sigma(p^{k})\,s, \qquad \sigma(m^2) = p^{k}s$$
--
--   cannot both hold.
--
--   This is the residual part of the odd-index Dris problem at special exponents $k \ge 13$. When $k+1$ has at most one odd prime divisor, the relations are already excluded for a prime index $s$ (`OddPerfectNumber.no_dris_index_odd_prime_of_one_odd_prime`) and are reduced to the composite-index statement (`OddPerfectNumber.no_dris_index_odd_composite_of_one_odd_prime`). The counting obstruction behind those results bounds the prime support of $m$ by the primes dividing $k+1$, the primes of $s$, and one exceptional prime for each prime power of $s$; a second odd prime divisor of $k+1$ makes that bound too weak to contradict Sylvester's bound $\omega(N) \ge 5$, which is why this case is separated out. The smallest exponents it concerns are $k = 29$, where $k+1 = 30 = 2\cdot 3\cdot 5$, and $k = 41$, where $k+1 = 42 = 2 \cdot 3 \cdot 7$.
-- source:
--   J. A. B. Dris, The abundancy index of divisors of odd perfect numbers, Journal of Integer Sequences 15 (2012), Article 12.4.4, Section 2 (Dris parametrisation of the Euler equation); Euler form and special-exponent case k >= 13 as recorded on the Odd Perfect Number Conjecture mission; residual case after OddPerfectNumber.no_dris_index_odd_prime_of_one_odd_prime and OddPerfectNumber.no_dris_index_odd_composite_of_one_odd_prime.

import Mathlib

namespace OddPerfectNumber

theorem no_dris_thirteen_s_ge_two_two_odd_primes (p k m s : Nat) (hp : p.Prime) (hp2 : p != 2)
    (hp4 : p % 4 = 1) (hk4 : k % 4 = 1) (hk13 : 13 ≤ k) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hs2 : 2 ≤ s) (hs_not_even : ¬ Even s)
    (hk1 : 2 ≤ ((k + 1).primeFactors.erase 2).card) :
    ¬ (2 * m ^ 2 = (∑ d ∈ (p ^ k).divisors, d) * s ∧
      (∑ d ∈ (m ^ 2).divisors, d) = p ^ k * s) := by
  sorry

end OddPerfectNumber
