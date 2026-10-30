-- Prove2me | Theorems.Thm_LL_Decomp1543c_S1_absorb
-- name    : LL_Decomp1543c.S1_absorb
-- status  : Open
-- author  : @sthubbar
-- created : 2026-10-29T17:33:59.533094+00:00
-- url     : https://prove2.me/theorems/8cb8f542-942c-459e-b555-392c9a52d133
-- title:
--   Absorbing $S_1$ into the middle term
-- statement:
--   For natural $N$ with $\log N\ge3100$ and $U=N^{2/5}(\log N)^{-4/5}$, one has $1.02\,U\le0.38\,N^{4/5}(\log N)^{1.4}$.
-- source:
--   M. C. Liu and T. Z. Wang, On the Vinogradov bound in the three primes Goldbach conjecture, Acta Arith. 105, 2002, p. 168, absorption of S1 in the middle term of (6.2). https://doi.org/10.4064/aa105-2-3

import Mathlib
import Definitions.Def_LL_Decomp1543c_Uf

open Real Finset ArithmeticFunction

namespace LL_Decomp1543c
theorem S1_absorb (N : ℕ) (hL : 3100 ≤ Real.log N) :
    1.02 * Uf N ≤ 0.38 * (N : ℝ) ^ ((4 : ℝ) / 5) * Real.log N ^ (1.4 : ℝ) := by sorry
end LL_Decomp1543c
