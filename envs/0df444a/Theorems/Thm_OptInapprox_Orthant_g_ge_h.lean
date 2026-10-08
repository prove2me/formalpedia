-- Prove2me | Theorems.Thm_OptInapprox_Orthant_g_ge_h
-- name    : OptInapprox.Orthant.g_ge_h
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:30:17.821932+00:00
-- url     : https://prove2.me/theorems/cba7b04e-2f81-4839-9984-367d86b368c7
-- title:
--   Proof of Proposition 6.1, p. 30 — on u, v ≥ 0 the exponent g(u, v) dominates h(u, v)
-- statement:
--   Let $0\le\rho<1$ and $t>0$, and let
--   $$g(u,v)=\frac{u+v}{1+\rho}+\frac{(u-v)^2+2(1-\rho)uv}{2(1-\rho^2)t^2},\qquad h(u,v)=\frac{u+v}{1+\rho}+\frac{(u-v)^2}{2(1-\rho^2)t^2}.$$
--   Then for all $u,v\ge0$,
--   $$g(u,v)\ \ge\ h(u,v).$$
--
--   On the quadrant of integration of (18) this lets $g$ be replaced by the simpler exponent $h$, at the cost of an inequality; it is the only place where the proof of Proposition 6.1 loses anything.
-- source:
--   Khot, Kindler, Mossel & O'Donnell, Optimal Inapproximability Results for MAX-CUT and Other 2-Variable CSPs?, SIAM J. Comput. 37(1), 2007 (authors' version of February 7, 2007), p. 30, proof of Proposition 6.1 (the sentence after (18))

import Mathlib
import Definitions.Def_OptInapprox_Orthant_Setting

open MeasureTheory ProbabilityTheory

namespace OptInapprox.Orthant

/-- Proof of Proposition 6.1, p. 30: on `u, v ≥ 0`, `g(u, v) ≥ h(u, v)`. -/
theorem g_ge_h (t ρ u v : ℝ) (ht : 0 < t) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    hExp ρ t u v ≤ gExp ρ t u v := by sorry

end OptInapprox.Orthant
