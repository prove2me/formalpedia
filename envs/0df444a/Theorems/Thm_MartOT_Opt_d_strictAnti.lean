-- Prove2me | Theorems.Thm_MartOT_Opt_d_strictAnti
-- name    : MartOT.Opt.d_strictAnti
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:20:44.808381+00:00
-- url     : https://prove2.me/theorems/83cc953d-2823-4674-b022-01cce7e34b36
-- title:
--   Proof of Theorem 6.1, (15), p. 37 — d(t) = λh(y⁺ − t) + (1 − λ)h(y⁻ − t) − h(y′ − t) is strictly decreasing when h′ is strictly convex
-- statement:
--   Let $h:\mathbb R\to\mathbb R$ be differentiable with strictly convex derivative $h'$. Let $y^-<y'<y^+$ and $\lambda\in(0,1)$ with $\lambda y^+ + (1-\lambda)y^- = y'$. Then the function
--
--   $$d(t)=\lambda\,h(y^+-t)+(1-\lambda)\,h(y^--t)-h(y'-t),\qquad t\in\mathbb R,$$
--
--   is strictly decreasing on $\mathbb R$.
--
--   For the cost $c(x,y)=h(y-x)$ this is the function (15), $d(t)=\lambda c(t,y^+)+(1-\lambda)c(t,y^-)-c(t,y')$; its monotonicity is the analytic heart of the optimality of the left-curtain coupling.
-- source:
--   arXiv:1208.1509v2, proof of Theorem 6.1, display (15) and the lines after it, p. 37

import Mathlib
import Definitions.Def_MartOT_Var_Setting

namespace MartOT.Opt

open MeasureTheory

theorem d_strictAnti (h : ℝ → ℝ) (hd : Differentiable ℝ h)
    (hconv : StrictConvexOn ℝ Set.univ (deriv h)) (ym yp y' l : ℝ)
    (hym : ym < y') (hyp : y' < yp) (hl0 : 0 < l) (hl1 : l < 1)
    (hcomb : l * yp + (1 - l) * ym = y') :
    StrictAnti (fun t : ℝ => l * h (yp - t) + (1 - l) * h (ym - t) - h (y' - t)) := by sorry

end MartOT.Opt
