-- Prove2me | Theorems.Thm_Helfgott_circle_arc_integral_scaled
-- name    : Helfgott.circle_arc_integral_scaled
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-05T04:47:21.837606+00:00
-- url     : https://prove2.me/theorems/339ab2f1-aab2-47d9-b1e5-92cff9f55db7
-- title:
--   Exact scaled real parametrization of a short additive-circle arc integral
-- statement:
--   For an arbitrary complex-valued function $f$ on the unit additive circle, a real center $c$, a radius $0\le\varepsilon\le1/2$, and a positive scale $x$, normalized Haar integration over the open circle ball satisfies
--
--   $$\int_{\operatorname{dist}(\alpha,c)<\varepsilon}f(\alpha)\,d\alpha
--   =\frac1x\int_{-x\varepsilon}^{x\varepsilon}f(c+\beta/x\bmod1)\,d\beta.$$
--
--   The identity is formulated for Bochner integrals and requires no additional continuity or integrability assumption. Circle arcs crossing a representative interval's seam are included. The closed endpoints on the real side do not affect the integral. This change of variables gives the exact scale and Jacobian when individual Goldbach major-arc integrals are converted to real Fourier integrals.
-- source:
--   Mathlib’s additive-circle fundamental-domain integration and interval-integral affine change of variables. Applied to the major-arc coordinates of H. A. Helfgott, The ternary Goldbach conjecture is true, https://arxiv.org/html/1312.7748v2, §§3.3 and 7.2. Written by Codex.

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
open MeasureTheory Set Metric

namespace Helfgott

theorem circle_arc_integral_scaled (f : AddCircle (1:ℝ) → ℂ) (c ε x : ℝ)
    (hε0 : 0 ≤ ε) (hε : ε ≤ (1/2:ℝ)) (hx : 0 < x) :
    (∫ α in ball (c : AddCircle (1:ℝ)) ε,f α ∂AddCircle.haarAddCircle) =
      x⁻¹ • (∫ β in Icc (-(x*ε)) (x*ε),f ((c+β/x : ℝ) : AddCircle (1:ℝ))) := by sorry

end Helfgott
