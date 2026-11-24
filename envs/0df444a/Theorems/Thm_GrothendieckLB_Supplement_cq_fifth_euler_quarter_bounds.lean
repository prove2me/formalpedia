-- Prove2me | Theorems.Thm_GrothendieckLB_Supplement_cq_fifth_euler_quarter_bounds
-- name    : GrothendieckLB.Supplement.cq_fifth_euler_quarter_bounds
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T20:07:31.509426+00:00
-- url     : https://prove2.me/theorems/8cefbc9f-dca4-4ab0-8c1f-e3d6425d917c
-- title:
--   Four rational quadrant bounds for the fifth Euler derivative
-- statement:
--   Parameterize each angular quadrant by $\theta=2\arctan(s^2)$ and reflections, $0\le s\le1$. After multiplying the fifth Euler derivative by the normalized angular Jacobian, four uniform upper bounds on successive quarters of the parameter interval are $531000$, $545000$, $486000$, and $84000$. The radial parameter ranges from $99999/100000$ to one. Exact rational interval evaluation gives the four upper ceilings $530389$, $544424$, $485388$, and $83853$.
-- source:
--   Independent Price differentiation and rational interval certificate for Saha et al., arXiv:2608.11158v2. The density identity is Prove2Me bb4bfdfc-4dcc-425d-8a98-1b646de8d12b.

import Mathlib
import Definitions.Def_GrothendieckLB_Supplement_cqCorr

namespace GrothendieckLB.Supplement

theorem cq_fifth_euler_quarter_bounds (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (Metric.ball 0 1))
    (hreal : ∀ t : ℝ, |t| < 1 → F (t : ℂ) = (cqCorr 0.136419125 0.34101124 0.05276111 t : ℂ))
    (r s θ : ℝ) (hr : (99999 : ℝ) / 100000 ≤ r) (hr₁ : r < 1) (hs : s ∈ Set.Icc 0 1)
    (hθ : let a := 2 * Real.arctan (s^2)
          θ = a ∨ θ = Real.pi-a ∨ θ = Real.pi+a ∨ θ = 2*Real.pi-a) :
    let v := ((2 / Real.pi) * (4*s / (1+s^4))) *
      ‖(((fun g : ℂ → ℂ => fun w : ℂ => w * deriv g w)^[5]) F) (circleMap 0 r θ)‖
    (s ≤ 1/4 → v ≤ 531000) ∧
      (1/4 ≤ s → s ≤ 1/2 → v ≤ 545000) ∧
      (1/2 ≤ s → s ≤ 3/4 → v ≤ 486000) ∧
      (3/4 ≤ s → v ≤ 84000) := by sorry

end GrothendieckLB.Supplement
