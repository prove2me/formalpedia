-- Prove2me | Theorems.Thm_MartOT_Opt_reroute_cheaper
-- name    : MartOT.Opt.reroute_cheaper
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:19:25.472715+00:00
-- url     : https://prove2.me/theorems/1638e6f7-39c2-40f0-a9b3-b097dc85b15f
-- title:
--   Proof of Theorem 6.1, p. 37 — for c = h(y − x), h′ strictly convex, the rerouting of the forbidden configuration is strictly cheaper
-- statement:
--   Let $h:\mathbb R\to\mathbb R$ be differentiable with strictly convex derivative $h'$, and let $c(x,y)=h(y-x)$. Let $x<x'$, $y^-<y'<y^+$ and $\lambda\in(0,1)$ with $\lambda y^+ + (1-\lambda)y^- = y'$. Then
--
--   $$\lambda c(x,y^+)+(1-\lambda)c(x,y^-)+c(x',y')\;>\;\lambda c(x',y^+)+(1-\lambda)c(x',y^-)+c(x,y').$$
--
--   The left side is the cost of the three-point measure $\alpha$ sitting on the forbidden configuration $(x,y^-),(x,y^+),(x',y')$ of Definition 1.4, the right side the cost of its competitor $\alpha'$; so an optimal martingale plan cannot charge such a configuration.
--
--   **Formalization Note** The cost is a function $c$ with the hypothesis $c(x,y)=h(y-x)$ for all $x,y$. No measure appears; the statement is about real numbers.
-- source:
--   arXiv:1208.1509v2, proof of Theorem 6.1, p. 37 (unnumbered: "It leads to smaller costs if and only if …")

import Mathlib
import Definitions.Def_MartOT_Var_Setting

namespace MartOT.Opt

open MeasureTheory

theorem reroute_cheaper (h : ℝ → ℝ) (hd : Differentiable ℝ h)
    (hconv : StrictConvexOn ℝ Set.univ (deriv h)) (c : ℝ → ℝ → ℝ)
    (hc : ∀ x y, c x y = h (y - x)) (x x' ym yp y' l : ℝ) (hx : x < x')
    (hym : ym < y') (hyp : y' < yp) (hl0 : 0 < l) (hl1 : l < 1)
    (hcomb : l * yp + (1 - l) * ym = y') :
    l * c x yp + (1 - l) * c x ym + c x' y' > l * c x' yp + (1 - l) * c x' ym + c x y' := by sorry

end MartOT.Opt
