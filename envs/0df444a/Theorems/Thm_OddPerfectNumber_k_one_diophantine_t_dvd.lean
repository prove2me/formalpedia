-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_diophantine_t_dvd
-- name    : OddPerfectNumber.k_one_diophantine_t_dvd
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-11T06:16:23.825444+00:00
-- url     : https://prove2.me/theorems/4da00dde-e5d3-45f9-8bc7-830edfd480c9
-- title:
--   The k = 1 cofactor (p+1)/2 divides m^2
-- statement:
--   Let $p$ be prime with $p \equiv 1 \pmod 4$ and $m$ odd with $p \nmid m$, satisfying the bridge equation $(1+p)\sigma(m^2) = 2pm^2$. Write $t = (p+1)/2$. Then $t$ divides $m^2$. Indeed $t$ is odd and $\gcd(t, p) = 1$ (any common divisor divides $2t - p = 1$), while the bridge equation gives $t\sigma(m^2) = pm^2$, so $t \mid pm^2$ and coprimality forces $t \mid m^2$. With $d = m^2/t$ this yields $\sigma(m^2) = pd$, the entry point to the prime-factor valuation-flow analysis.
-- source:
--   Diophantine remainder of the special-exponent k = 1 case of the Odd Perfect Number Conjecture after the sigma-multiplicativity bridge; Euler structure theorem (L. Euler, De numeris amicabilibus, Opera postuma 1 (1849)). Divisibility reduction step of the factor-chain attack plan.

import Mathlib

namespace OddPerfectNumber

theorem k_one_diophantine_t_dvd (p m : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hpm : ¬ p ∣ m) (hm_odd : Odd m)
    (heq : (1 + p) * (∑ d ∈ (m ^ 2).divisors, d) = 2 * (p * m ^ 2)) :
    (p + 1) / 2 ∣ m ^ 2 := by
  sorry

end OddPerfectNumber
