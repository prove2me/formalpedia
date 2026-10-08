-- Prove2me | Theorems.Thm_Helfgott_singularConstant_bounds
-- name    : Helfgott.singularConstant_bounds
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-05T02:37:17.257713+00:00
-- url     : https://prove2.me/theorems/f50d0579-3002-4fac-9aed-cf5fed966b2e
-- title:
--   Uniform nonnegative upper bound for the actual ternary Euler constant
-- statement:
--   For every natural number $N$, the actual ternary Euler constant satisfies
--
--   $$0\le C_0(N)\le\frac83.$$
--
--   Here the local factor at a prime $p$ is $1-1/(p-1)^2$ when $p$ divides $N$, and $1+1/(p-1)^3$ otherwise; nonprime indices contribute $1$. The constant is the convergent product of these factors. No parity or positivity assumption on $N$ is needed.
--
--   This uniform upper bound controls absolute errors when the singular constant multiplies a smoothing approximation or another main-term perturbation. It complements the separate lower bound for odd arguments.
-- source:
--   H. A. Helfgott, The ternary Goldbach conjecture is true, https://arxiv.org/html/1312.7748v2, §7.2, equation (7.9), defining C0 and its local factors. The coarse upper bound 8/3 is independently derived from those exact factors by a complete inverse-cube telescoping estimate. Written by Codex.

import Definitions.Def_Helfgott_SingularSeries

theorem Helfgott.singularConstant_bounds (N : ℕ) :
    0 ≤ Helfgott.singularConstant N ∧ Helfgott.singularConstant N ≤ (8/3:ℝ) := by sorry
