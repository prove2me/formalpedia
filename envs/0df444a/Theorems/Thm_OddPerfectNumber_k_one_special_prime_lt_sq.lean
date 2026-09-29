-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_special_prime_lt_sq
-- name    : OddPerfectNumber.k_one_special_prime_lt_sq
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-11T13:09:00.121+00:00
-- url     : https://prove2.me/theorems/37edeadf-4c48-455d-84f9-65586e205254
-- title:
--   Special exponent $k=1$: $1098\,p < m^{2}$
-- statement:
--   Let $N = p\,m^{2}$ be an odd perfect number in Euler form with special exponent $k = 1$ (the configuration predicted by the Descartes–Frenicle–Sorli conjecture): $p$ is prime, $m$ is odd, $p \nmid m$, and the Dris relations
--
--   $$2m^{2} = \sigma(p)\,s, \qquad \sigma(m^{2}) = p\,s$$
--
--   hold, with $s = \sigma(m^{2})/p$ the Dris index. Then the special prime is small compared with the square part:
--
--   $$1098\,p \ <\ m^{2}.$$
--
--   Trivially $\sigma(p) = p+1$ divides $2m^{2}$, which alone gives only $p < 2m^{2}$. The point of the statement is the explicit constant: it comes from a lower bound $s \ge 13^{3} = 2197$ for the Dris index at $k = 1$, since $2m^{2} = (p+1)s$. That lower bound in turn is a counting statement: at $k = 1$ the divisor sum $\sigma(m^{2}) = p\,s$ has $p$-adic valuation $1$, so at most one of the local divisor sums $\sigma(q^{2v_q(m)})$, $q \mid m$, is divisible by $p$, and each of the others is a factor of $s$ of size at least $1 + q + q^{2} \ge 13$. Sylvester's bound $\omega(N) \ge 5$ leaves at least three such factors.
--
--   The result is unconditional given the two Dris relations: no congruence conditions on $p$, $m$ or $s$ are assumed.
-- source:
--   J. A. B. Dris, The abundancy index of divisors of odd perfect numbers, Journal of Integer Seq. 15 (2012), Article 12.4.4, Section 2 (Dris parametrisation); J. J. Sylvester (1888) for omega(N) >= 5.

import Mathlib

namespace OddPerfectNumber

theorem k_one_special_prime_lt_sq (p m s : Nat)
    (hp : p.Prime) (hm : Odd m) (hpm : ¬ p ∣ m)
    (h1 : 2 * m ^ 2 = (∑ d ∈ p.divisors, d) * s)
    (h2 : (∑ x ∈ (m ^ 2).divisors, x) = p * s) :
    1098 * p < m ^ 2 := by
  sorry

end OddPerfectNumber
