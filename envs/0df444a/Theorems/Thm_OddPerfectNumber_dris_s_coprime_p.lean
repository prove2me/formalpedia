-- Prove2me | Theorems.Thm_OddPerfectNumber_dris_s_coprime_p
-- name    : OddPerfectNumber.dris_s_coprime_p
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-11T08:27:38.233888+00:00
-- url     : https://prove2.me/theorems/ed6a399b-d6d5-48f2-a648-3c1d2fef0e97
-- title:
--   The Dris index s is coprime to the special prime p
-- statement:
--   Let $p$ be an odd prime, let $m$ with $p \nmid m$, and suppose $2m^2 = \sigma(p^k)s$ where $\sigma$ is the sum-of-divisors function. Then $p \nmid s$. Indeed $p \mid s$ would give $p \mid 2m^2$, whence primality forces $p \mid 2$ or $p \mid m$, i.e. $p = 2$ or a contradiction. This is the coprimality fact behind the exact valuation $v_p(\sigma(m^2)) = k$ in the Dris analysis: with $\sigma(m^2) = p^ks$ and $p \nmid s$, the full $p$-adic content of $\sigma(m^2)$ sits in $p^k$.
-- source:
--   Dris-index analysis of the Odd Perfect Number Conjecture; Euler structure theorem (L. Euler, De numeris amicabilibus, Opera postuma 1 (1849)).

import Mathlib

namespace OddPerfectNumber

theorem dris_s_coprime_p (p k m s : Nat) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpm : ¬ p ∣ m)
    (h : 2 * m ^ 2 = (∑ d ∈ (p ^ k).divisors, d) * s) : ¬ p ∣ s := by
  sorry

end OddPerfectNumber
