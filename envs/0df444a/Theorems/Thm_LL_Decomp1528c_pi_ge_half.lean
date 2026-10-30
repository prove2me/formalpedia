-- Prove2me | Theorems.Thm_LL_Decomp1528c_pi_ge_half
-- name    : LL_Decomp1528c.pi_ge_half
-- status  : Open
-- author  : @sthubbar
-- created : 2026-10-29T15:30:38.136668+00:00
-- url     : https://prove2.me/theorems/a256c1ce-6eb7-41b3-8d16-9a3f2810ff63
-- title:
--   Explicit lower bound for the prime-counting function
-- statement:
--   For every real number $x\ge11$, $\pi(x)\ge x/(2\log x)$, where $\pi(x)$ counts primes at most $\lfloor x\rfloor$.
-- source:
--   Lab unit U-1528, classical Chebyshev bounds; source context: P. J. Campbell 2026, https://arxiv.org/abs/2608.09488v1. Exact range and constant as stated in Decomp1528c.lean.

import Mathlib

open Real Finset Chebyshev

namespace LL_Decomp1528c
theorem pi_ge_half {x : ℝ} (hx : 11 ≤ x) : x / (2 * log x) ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) := by sorry
end LL_Decomp1528c
