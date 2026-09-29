-- Prove2me | Theorems.Thm_OddPerfectNumber_dris_index_lte_support_bound
-- name    : OddPerfectNumber.dris_index_lte_support_bound
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-11T13:19:56.662259+00:00
-- url     : https://prove2.me/theorems/bbae1c39-0f24-46d2-b067-be4e78110fee
-- title:
--   Dris configuration: $\omega(m)\le\omega(s)+\Omega(s)+\#\{q\mid k+1\}$
-- statement:
--   Let $p$ be prime, $m$ odd with $p \nmid m$, and suppose the Dris relations
--
--   $$2m^{2} = \sigma(p^{k})\,s, \qquad \sigma(m^{2}) = p^{k}\,s$$
--
--   hold, with Dris index $s$. Then the prime support of $m$ obeys
--
--   $$\omega(m) \ \le\ \omega(s) + \Omega(s) + \#\{\,q \text{ odd prime} : q \mid k+1\,\},$$
--
--   where $\omega$ counts distinct prime factors and $\Omega$ counts them with multiplicity.
--
--   The three terms correspond to a trichotomy for a prime $q \mid m$. If $q \mid s$, it is counted by $\omega(s)$. If $q \nmid s$, then $q^{2} \mid \sigma(p^{k})$, because $q^{2} \mid m^{2}$ and $s$ is prime to $q$; moreover the local divisor sum $\sigma(q^{2v_q(m)})$ divides $\sigma(m^{2}) = p^{k}s$. If that local sum is prime to $s$ it is a power of $p$, and lifting the exponent forces $q \mid k+1$ — the third term. Otherwise it contributes a prime factor of $s$, and these contributions, taken one per prime, multiply to a divisor of $s$, so they number at most $\Omega(s)$.
--
--   Combined with Sylvester's bound $\omega(N) \ge 5$, which gives $\omega(m) \ge 4$, the inequality is the general form of the known impossibility of a Dris index equal to $1$ or to an odd prime when $k+1$ has at most one odd prime factor: those cases have $\omega(s)+\Omega(s) \le 2$. It is stated with no congruence hypotheses on $p$, $k$ or $s$.
-- source:
--   J. A. B. Dris, The abundancy index of divisors of odd perfect numbers, Journal of Integer Seq. 15 (2012), Article 12.4.4, Section 2 (Dris parametrisation); the lifting-the-exponent step is the one used in G. G. Dandapat, J. L. Hunsucker, C. Pomerance, Some new results on odd perfect numbers, Pacific J. Math. 57 (1975), 359-364, Theorem 1.

import Mathlib

namespace OddPerfectNumber

theorem dris_index_lte_support_bound (p k m s : Nat)
    (hp : p.Prime) (hm : Odd m) (hpm : ¬ p ∣ m)
    (h1 : 2 * m ^ 2 = (∑ d ∈ (p ^ k).divisors, d) * s)
    (h2 : (∑ x ∈ (m ^ 2).divisors, x) = p ^ k * s) :
    m.primeFactors.card ≤
      s.primeFactors.card + s.primeFactorsList.length + ((k + 1).primeFactors.erase 2).card := by
  sorry

end OddPerfectNumber
