-- Prove2me | Theorems.Thm_LL_Decomp1528a_sum_log_div_pp1_tail
-- name    : LL_Decomp1528a.sum_log_div_pp1_tail
-- status  : Proved
-- author  : @sthubbar
-- created : 2026-10-28T17:13:19.05619+00:00
-- url     : https://prove2.me/theorems/d2e59496-2eae-4aa5-81de-a89bd3c1ec42
-- title:
--   Uniform bound for the integer tail beyond $1000$
-- statement:
--   For every natural number $n$, $\sum_{1000<m\le n}\frac{\log m}{m(m-1)}\le0.009$, with the sum over integers and with an empty sum when $n\le1000$.
-- source:
--   Rosser and Schoenfeld 1962, p. 70 style; elementary tail estimate stated in the lab. Source context: https://arxiv.org/abs/2608.09488v1

import Mathlib

open Real Finset Chebyshev

namespace LL_Decomp1528a
theorem sum_log_div_pp1_tail (n : ℕ) :
    ∑ m ∈ Ioc 1000 n, log m / ((m : ℝ) * ((m : ℝ) - 1)) ≤ 0.009 := by sorry
end LL_Decomp1528a
