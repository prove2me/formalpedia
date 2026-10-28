-- Prove2me | Theorems.Thm_LL_Decomp1528a_vonMangoldt_sum_le
-- name    : LL_Decomp1528a.vonMangoldt_sum_le
-- status  : Proved
-- author  : @sthubbar
-- created : 2026-10-28T17:14:31.960252+00:00
-- url     : https://prove2.me/theorems/ca45bca5-1efd-4fc9-acaa-ce1af30fa297
-- title:
--   Upper bound for the weighted von Mangoldt sum
-- statement:
--   For every natural number $n$, $n\sum_{m=1}^{n}\frac{\Lambda(m)}{m}\le\log(n!)+\psi(n)$, where $\Lambda$ is the von Mangoldt function and $\psi(n)=\sum_{m=1}^{n}\Lambda(m)$. The statement includes $n=0$.
-- source:
--   Montgomery and Vaughan, Multiplicative Number Theory I, Section 2.2; lab unit U-1528. Source context: https://arxiv.org/abs/2608.09488v1

import Mathlib

open Real Finset Chebyshev

namespace LL_Decomp1528a
theorem vonMangoldt_sum_le (n : ℕ) :
    (n : ℝ) * ∑ m ∈ Icc 1 n, ArithmeticFunction.vonMangoldt m / m ≤
      log (n.factorial : ℝ) + ψ n := by sorry
end LL_Decomp1528a
