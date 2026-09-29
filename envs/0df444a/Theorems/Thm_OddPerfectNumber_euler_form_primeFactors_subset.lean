-- Prove2me | Theorems.Thm_OddPerfectNumber_euler_form_primeFactors_subset
-- name    : OddPerfectNumber.euler_form_primeFactors_subset
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-11T09:04:01.119394+00:00
-- url     : https://prove2.me/theorems/92ded677-10ef-44d1-aedd-5c5b40c6d4ba
-- title:
--   Prime support of Euler-form numbers lies in p plus the support of m
-- statement:
--   Let $p$ be prime and let $m \ne 0$. Then every prime divisor of a number in Euler form $p^k m^2$ is either $p$ itself or a prime divisor of $m$. Combined with a bound on the prime support of $m$, this yields the distinct-prime-factor counts that feed global bounds such as Sylvester’s $\omega(N) \ge 5$ for odd perfect numbers. It is the bookkeeping step closing every Sylvester-contradiction finale.
-- source:
--   Bookkeeping for the Sylvester-contradiction finales of the Odd Perfect Number Conjecture in Euler form (L. Euler, De numeris amicabilibus, Opera postuma 1 (1849)).

import Mathlib

namespace OddPerfectNumber

theorem euler_form_primeFactors_subset (p k m : Nat) (hp : p.Prime)
    (hm : m ≠ 0) :
    (p ^ k * m ^ 2).primeFactors ⊆ {p} ∪ m.primeFactors := by
  sorry

end OddPerfectNumber
