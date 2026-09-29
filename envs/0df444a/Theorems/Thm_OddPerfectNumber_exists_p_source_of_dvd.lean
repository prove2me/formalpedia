-- Prove2me | Theorems.Thm_OddPerfectNumber_exists_p_source_of_dvd
-- name    : OddPerfectNumber.exists_p_source_of_dvd
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-11T09:09:46.301228+00:00
-- url     : https://prove2.me/theorems/29082f61-bf54-4121-aef3-b26022e8da88
-- title:
--   A prime power dividing a divisor sum supplies a local source
-- statement:
--   Let $p$ be prime and suppose $p^k$ with $k \ge 1$ divides the divisor sum $\sigma(m^2)$. Then some prime power in the support of $m^2$ supplies $p$: there is $q$ in the prime factors of $m^2$ with $p$ dividing the local geometric sum $1 + q + \cdots + q^{2e}$. Since $p^k \mid \sigma(m^2)$ forces $p \mid \sigma(m^2)$, and the divisor sum factors over the prime support, primality extracts one supplied local factor. This is the existence half of the source analysis at general exponent (uniqueness can fail for $k > 1$, so only existence is stated).
-- source:
--   Valuation-flow analysis of the Odd Perfect Number Conjecture at general special exponent; Euler structure theorem (L. Euler, De numeris amicabilibus, Opera postuma 1 (1849)).

import Mathlib

namespace OddPerfectNumber

theorem exists_p_source_of_dvd (p k m : Nat) (hp : p.Prime) (hk : 1 ≤ k)
    (hm2 : m ^ 2 ≠ 0)
    (hdvd : p ^ k ∣ (∑ x ∈ (m ^ 2).divisors, x)) :
    ∃ q ∈ (m ^ 2).primeFactors,
      p ∣ ∑ i ∈ Finset.range ((m ^ 2).factorization q + 1), q ^ i := by
  sorry

end OddPerfectNumber
