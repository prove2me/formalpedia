-- Prove2me | Theorems.Thm_LL_Decomp1543a_block_cauchy
-- name    : LL_Decomp1543a.block_cauchy
-- status  : Open
-- author  : @sthubbar
-- created : 2026-10-29T15:38:33.292418+00:00
-- url     : https://prove2.me/theorems/aeab5a83-a44b-4217-b861-b7c8142a74bb
-- title:
--   Cauchy bound for a Möbius-weighted sum
-- statement:
--   For every finite $T\subset\mathbb N$ and function $z:\mathbb N\to\mathbb C$, $\left|\sum_{t\in T}\mu(t)z(t)\right|\le\sqrt{\sum_{t\in T}|\mu(t)|}\sqrt{\sum_{t\in T}|z(t)|^2}$.
-- source:
--   M. C. Liu and T. Z. Wang, On the Vinogradov bound in the three primes Goldbach conjecture, Acta Arith. 105, 2002, p. 170, equation 6.11. https://doi.org/10.4064/aa105-2-3

import Mathlib

open Real Finset ArithmeticFunction

namespace LL_Decomp1543a
theorem block_cauchy (T : Finset ℕ) (z : ℕ → ℂ) :
    ‖∑ t ∈ T, (moebius t : ℂ) * z t‖ ≤
      √(∑ t ∈ T, |(moebius t : ℝ)|) * √(∑ t ∈ T, ‖z t‖ ^ 2) := by sorry
end LL_Decomp1543a
