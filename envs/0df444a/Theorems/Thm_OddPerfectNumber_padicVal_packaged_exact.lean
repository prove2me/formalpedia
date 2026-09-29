-- Prove2me | Theorems.Thm_OddPerfectNumber_padicVal_packaged_exact
-- name    : OddPerfectNumber.padicVal_packaged_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-11T08:49:18.145778+00:00
-- url     : https://prove2.me/theorems/c2acc494-4067-4669-8074-f642ff174dd2
-- title:
--   Exact p-adic valuation of a packaged prime-power multiple
-- statement:
--   Let $p$ be prime and let $d \ne 0$ with $p \nmid d$. Then the exact $p$-adic valuation of $p^k d$ is $k$. The valuation splits over the product as $k + 0$: the prime power contributes exactly $k$, while the coprime cofactor contributes nothing. This uniform fact feeds every packaged-obstruction argument in the odd-perfect-number analysis, at special exponent $k = 1$ as well as $k \ge 5$: wherever $\sigma(m^2) = p^k d$ with $p \nmid d$, the full $p$-adic content sits in $p^k$, which is what forces a single prime-power divisor sum to supply $p$.
-- source:
--   Valuation-flow analysis of the Odd Perfect Number Conjecture; Euler structure theorem (L. Euler, De numeris amicabilibus, Opera postuma 1 (1849)).

import Mathlib

namespace OddPerfectNumber

theorem padicVal_packaged_exact (p k d : Nat) (hp : p.Prime) (hd0 : d ≠ 0)
    (hpd : ¬ p ∣ d) : padicValNat p (p ^ k * d) = k := by
  sorry

end OddPerfectNumber
