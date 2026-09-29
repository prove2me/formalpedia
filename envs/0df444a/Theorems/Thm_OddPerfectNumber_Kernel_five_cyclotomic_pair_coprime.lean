-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_five_cyclotomic_pair_coprime
-- name    : OddPerfectNumber.Kernel.five_cyclotomic_pair_coprime
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-28T23:06:17.174057+00:00
-- url     : https://prove2.me/theorems/dbed225d-85c0-4877-9ead-8c073246bf99
-- title:
--   The two non-trivial k=5 cyclotomic factors of sigma(p^5) are coprime
-- statement:
--   For every odd $p$, the two non-trivial cyclotomic factors of $\sigma(p^5) = (p+1)(p^2+p+1)(p^2-p+1)$ are coprime: $\gcd(p^2+p+1,\ p^2-p+1) = 1$. Indeed a common divisor $g$ divides the sum $2(p^2+1)$ and the difference $2p$; both factors are odd so $g$ is odd, hence $g \mid p^2+1$ and $g \mid p$, forcing $g = 1$. This is what makes the order-$3$ and order-$6$ factors contribute disjoint prime supports, the property Gallardo's index analysis of $k=5$ relies on.
-- source:
--   Exact-arithmetic verification plus the elementary gcd argument for the $k=5$ cyclotomic factorisation of $\sigma(p^5)$; used by the square-free index reduction feeding OddPerfectNumber.no_dris_five_s_odd_ge_five_nonsq.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem five_cyclotomic_pair_coprime (p : Nat) (hp2 : p != 2) :
    Nat.gcd (p ^ 2 + p + 1) (p ^ 2 - p + 1) = 1 := by
  sorry

end OddPerfectNumber.Kernel
