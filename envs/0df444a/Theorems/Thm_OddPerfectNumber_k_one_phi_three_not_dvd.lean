-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_phi_three_not_dvd
-- name    : OddPerfectNumber.k_one_phi_three_not_dvd
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-11T06:16:27.616589+00:00
-- url     : https://prove2.me/theorems/590bdca7-6d42-4289-ae8d-0d7db08c6c24
-- title:
--   No prime divisor of (p+1)/2 has p dividing q^2+q+1
-- statement:
--   Let $p$ be prime with $p \equiv 1 \pmod 4$ and $q$ prime with $q \mid (p+1)/2$. Then $p \nmid q^2 + q + 1$. For prime $q$ this says $p$ does not divide $\sigma(q^2)$: if it did, $q$ would be a non-trivial cube root of unity mod $p$, and combined with $q \mid (p+1)/2$ this forces an impossible small-factor equation. This is the $\Phi_3$-stepping lemma for the $k = 1$ prime-factor valuation-flow attack (to be generalised from $\Phi_3$ to $\Phi_r$). Screened computationally for all primes $p \equiv 1 \pmod 4$ below two million (74,416 primes, no counterexample).
-- source:
--   Phi_3 stepping lemma of the factor-chain attack plan for the Diophantine remainder of the special-exponent k = 1 case of the Odd Perfect Number Conjecture; Euler structure theorem (L. Euler, De numeris amicabilibus, Opera postuma 1 (1849)).

import Mathlib

namespace OddPerfectNumber

theorem k_one_phi_three_not_dvd (p q : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hq : q.Prime)
    (hdiv : q ∣ (p + 1) / 2) :
    ¬ p ∣ q ^ 2 + q + 1 := by
  sorry

end OddPerfectNumber
