-- Prove2me | Theorems.Thm_OddPerfectNumber_prime_not_dvd_of_ne
-- name    : OddPerfectNumber.prime_not_dvd_of_ne
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-11T09:26:40.158994+00:00
-- url     : https://prove2.me/theorems/d64d3cb7-8c18-480a-8622-ed933f3b2a25
-- title:
--   A prime does not divide a distinct prime
-- statement:
--   Distinct primes do not divide each other: if $p$ and $q$ are prime with $q \neq p$ then $p \nmid q$. This is the nonvanishing fact every modular/order argument on the OPN cores needs before moving a prime cofactor into $\mathbf{Z}/p$.
-- source:
--   Valuation-flow analysis of the Odd Perfect Number Conjecture; Euler structure theorem (L. Euler, De numeris amicabilibus, Opera postuma 1 (1849)).

import Mathlib

namespace OddPerfectNumber

theorem prime_not_dvd_of_ne (p q : Nat)
    (hp : p.Prime) (hq : q.Prime) (hqp : q ≠ p) :
    ¬ p ∣ q := by
  sorry

end OddPerfectNumber
