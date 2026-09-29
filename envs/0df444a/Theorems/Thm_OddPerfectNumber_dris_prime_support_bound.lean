-- Prove2me | Theorems.Thm_OddPerfectNumber_dris_prime_support_bound
-- name    : OddPerfectNumber.dris_prime_support_bound
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-11T12:50:35.852023+00:00
-- url     : https://prove2.me/theorems/d4d685b8-bae5-442a-bc78-cd3d7b780f64
-- title:
--   Dris configuration: $\omega(m) \le k + \Omega(s)$
-- statement:
--   Let $p$ be a prime, let $m$ be odd with $p \nmid m$, and suppose the two Dris relations
--
--   $$2m^{2} = \sigma(p^{k})\,s, \qquad \sigma(m^{2}) = p^{k}\,s$$
--
--   hold, so that $s = \sigma(m^{2})/p^{k}$ is the Dris index of the configuration. (These relations say exactly that $N = p^{k}m^{2}$ is perfect.) Then the number of *distinct* primes dividing $m$ is bounded by
--
--   $$\omega(m) \le k + \Omega(s),$$
--
--   where $\Omega(s)$ counts the prime factors of $s$ with multiplicity (in Lean, the length of `s.primeFactorsList`).
--
--   The bound is an exact count of how the local divisor sums of $m^{2}$ distribute over the two factors of $\sigma(m^{2}) = p^{k}s$. Writing $\sigma(m^{2}) = \prod_{q \mid m}\sigma(q^{2v_q(m)})$, call a prime $q \mid m$ a *$p$-source* if $p \mid \sigma(q^{2v_q(m)})$. Since $s \mid m^{2}$ and $p \nmid m$, the index $s$ is prime to $p$, so the product of one copy of $p$ per $p$-source divides $p^{k}$: there are at most $k$ of them. Every prime $q \mid m$ that is not a $p$-source has $\sigma(q^{2v_q(m)}) > 1$ dividing $s$, and these local sums are pairwise coprime factors of $s$, so there are at most $\Omega(s)$ of them.
--
--   The bound is attained: for $m = 15$, $\sigma(m^{2}) = 403 = 13 \cdot 31$ has $\omega(m) = 2 = 1 + \Omega(31)$.
-- source:
--   J. A. B. Dris, The abundancy index of divisors of odd perfect numbers, Journal of Integer Seq. 15 (2012), Article 12.4.4, Section 2 (Dris parametrisation); the counting bound itself is proved here from the parametrisation.

import Mathlib

namespace OddPerfectNumber

theorem dris_prime_support_bound (p k m s : Nat)
    (hp : p.Prime) (hm : Odd m) (hpm : ¬ p ∣ m)
    (h1 : 2 * m ^ 2 = (∑ d ∈ (p ^ k).divisors, d) * s)
    (h2 : (∑ x ∈ (m ^ 2).divisors, x) = p ^ k * s) :
    m.primeFactors.card ≤ k + s.primeFactorsList.length := by
  sorry

end OddPerfectNumber
