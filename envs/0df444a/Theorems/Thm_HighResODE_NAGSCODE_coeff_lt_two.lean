-- Prove2me | Theorems.Thm_HighResODE_NAGSCODE_coeff_lt_two
-- name    : HighResODE.NAGSCODE.coeff_lt_two
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T15:36:32.054472+00:00
-- url     : https://prove2.me/theorems/9aa31df7-d1f6-42c5-a327-d72a72b6c6fc
-- title:
--   Proof of Theorem 1, p. 14 — 1/2 + (3 − 2√(μs) + μs)/(2(1+√(μs))³) + 2μs/(1+√(μs)) < 2 for 0 < μs ≤ 1
-- statement:
--   Let $\mu>0$ and $s>0$ with $\mu s\le1$. Then
--   $$\frac12+\frac{3-2\sqrt{\mu s}+\mu s}{2\big(1+\sqrt{\mu s}\big)^3}+\frac{2\mu s}{1+\sqrt{\mu s}}<2.$$
--
--   In the proof of Theorem 1 the left-hand side is the coefficient of $\|x_0-x^\star\|^2e^{-\sqrt\mu t/4}/s$ obtained from (3.2) and the initial conditions; the inequality, applied with $\mu s\le\mu/L\le1$, replaces it by the constant $2$ of Theorem 1.
--
--   **Formalization Note.** The page derives $\mu s\le1$ from $s\le1/L$ and $\mu\le L$; the statement takes $\mu s\le1$ directly. The supremum of the left-hand side over $0<\mu s\le1$ equals $2$ and is approached only as $\mu s\to0$, so the strict inequality needs $\mu s>0$.
-- source:
--   Shi, Du, Jordan & Su, Understanding the Acceleration Phenomenon via High-Resolution Differential Equations, arXiv:1810.08907v3, p. 14, proof of Theorem 1 (coefficient bound)

import Mathlib
import Definitions.Def_HighResODE_NAGSCODE_Setting

open scoped InnerProductSpace

namespace HighResODE.NAGSCODE

theorem coeff_lt_two (μ s : ℝ) (hμ : 0 < μ) (hs : 0 < s) (hμs : μ * s ≤ 1) :
    1 / 2 + (3 - 2 * Real.sqrt (μ * s) + μ * s) / (2 * (1 + Real.sqrt (μ * s)) ^ 3)
      + 2 * μ * s / (1 + Real.sqrt (μ * s)) < 2 := by sorry

end HighResODE.NAGSCODE
