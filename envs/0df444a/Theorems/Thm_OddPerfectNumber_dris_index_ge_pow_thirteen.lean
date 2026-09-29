-- Prove2me | Theorems.Thm_OddPerfectNumber_dris_index_ge_pow_thirteen
-- name    : OddPerfectNumber.dris_index_ge_pow_thirteen
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-11T19:17:59.337125+00:00
-- url     : https://prove2.me/theorems/b6e8bef6-6eaf-41ba-a62a-7cca90e8ff77
-- title:
--   Size of the Dris index: $13^{\\omega(m)-k} \\le s$
-- statement:
--   Consider the Dris parametrisation of the Euler equation: $p$ prime, $m$ odd with $p \nmid m$, and
--
--   $$2m^2 = \sigma(p^k)\,s, \qquad \sigma(m^2) = p^k s,$$
--
--   so that $s$ is the Dris index of the hypothetical odd perfect number $N = p^k m^2$. Then
--
--   $$13^{\,\omega(m) - k} \le s,$$
--
--   where $\omega(m)$ is the number of distinct prime divisors of $m$ (natural subtraction, so the statement is vacuous when $\omega(m) \le k$).
--
--   The reason is that $\sigma(m^2)$ factors as the product of the local divisor sums $\sigma(q^{2v_q(m)})$ over the primes $q \mid m$, and this product equals $p^k s$. At most $k$ of these local sums can be divisible by $p$; each of the remaining ones is a divisor of $s$ exceeding $1$, and in fact each is at least $1 + q + q^2 \ge 13$ because $q$ is an odd prime. Multiplying at least $\omega(m) - k$ such factors, all dividing the odd number $s$, gives the stated bound. Combined with Sylvester's bound $\omega(N) \ge 5$ (hence $\omega(m) \ge 4$) this is informative at small special exponents; at $k = 1$ it yields $s \ge 13^3 = 2197$.
-- source:
--   J. A. B. Dris, The abundancy index of divisors of odd perfect numbers, Journal of Integer Sequences 15 (2012), Article 12.4.4, Section 2 (Dris parametrisation); the counting argument is the one behind OddPerfectNumber.dris_prime_support_bound.

import Mathlib
open Finset

namespace OddPerfectNumber

theorem dris_index_ge_pow_thirteen (p k m s : Nat) (hp : p.Prime) (hm : Odd m) (hpm : ¬ p ∣ m)
    (h1 : 2 * m ^ 2 = (∑ d ∈ (p ^ k).divisors, d) * s)
    (h2 : (∑ x ∈ (m ^ 2).divisors, x) = p ^ k * s) :
    13 ^ (m.primeFactors.card - k) ≤ s := by
  sorry

end OddPerfectNumber
