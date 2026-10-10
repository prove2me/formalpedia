-- Prove2me | Theorems.Thm_HighResODE_HeavyBallODE_coeff_lt_seven_halves
-- name    : HighResODE.HeavyBallODE.coeff_lt_seven_halves
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:26:06.464255+00:00
-- url     : https://prove2.me/theorems/8d9d2144-6118-4588-97af-cbf02a431f52
-- title:
--   Proof of Theorem 2, p. 14 — for 0 < μs ≤ 1, 1/2 + 3/(1 + √(μs))³ + 2μs/(1 + √(μs)) < 7/2
-- statement:
--   Let $\mu>0$ and $s>0$ with $\mu s\le1$. Then
--   $$\frac12+\frac{3}{(1+\sqrt{\mu s})^3}+\frac{2\mu s}{1+\sqrt{\mu s}}<\frac72 .$$
--
--   In the paper this is applied with $0<\mu s\le\mu/L\le1$, which holds for $f\in\mathcal S^2_{\mu,L}$ and $s\le1/L$; it turns the explicit coefficient of the preceding bound into the constant $7/2$ of Theorem 2.
-- source:
--   Shi, Du, Jordan & Su, Understanding the Acceleration Phenomenon via High-Resolution Differential Equations, arXiv:1810.08907v3, p. 14, proof sketch of Theorem 2, final coefficient inequality

import Mathlib
import Definitions.Def_HighResODE_HeavyBallODE_Setting

namespace HighResODE.HeavyBallODE

theorem coeff_lt_seven_halves (μ s : ℝ) (hμ : 0 < μ) (hs : 0 < s) (hμs : μ * s ≤ 1) :
    1 / 2 + 3 / (1 + Real.sqrt (μ * s)) ^ 3 + 2 * μ * s / (1 + Real.sqrt (μ * s)) < 7 / 2 := by sorry

end HighResODE.HeavyBallODE
