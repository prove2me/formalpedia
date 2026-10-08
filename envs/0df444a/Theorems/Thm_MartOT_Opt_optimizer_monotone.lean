-- Prove2me | Theorems.Thm_MartOT_Opt_optimizer_monotone
-- name    : MartOT.Opt.optimizer_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:20:50.353006+00:00
-- url     : https://prove2.me/theorems/9d5e6a29-7744-4c8c-bdfd-3a8fab97f3c5
-- title:
--   Proof of Theorem 6.1, p. 37 — for c = h(y − x), h′ strictly convex, every optimizer of finite cost is left-monotone
-- statement:
--   Let $\mu,\nu$ be probability measures on $\mathbb R$ in convex order. Let $h:\mathbb R\to\mathbb R$ be differentiable with strictly convex derivative $h'$, and assume that $c(x,y)=h(y-x)$ satisfies the sufficient integrability condition $c(x,y)\ge a(x)+b(y)$ with $a\in L^1(\mu)$, $b\in L^1(\nu)$. Let $\pi\in\Pi_M(\mu,\nu)$ be an optimal martingale transport plan of finite cost, $\int c\,d\pi<+\infty$. Then $\pi$ is (left-)monotone in the sense of Definition 1.4: there is a Borel set $\Gamma$ with $\pi(\Gamma)=1$ such that
--
--   $$\text{there are no }(x,y^-),(x,y^+),(x',y')\in\Gamma\text{ with }x<x'\text{ and }y^-<y'<y^+.$$
--
--   This is the step that connects optimality to the geometry of the support; together with the uniqueness of monotone martingale plans it identifies every optimizer as the left-curtain coupling.
--
--   **Formalization Note** "Finite optimizer" is an optimal plan with cost $<+\infty$ in the extended reals.
-- source:
--   arXiv:1208.1509v2, proof of Theorem 6.1, p. 37 (unnumbered: "We have to show that every finite optimizer π is monotone.")

import Mathlib
import Definitions.Def_MartOT_Var_Setting

namespace MartOT.Opt

open MeasureTheory

theorem optimizer_monotone (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : MartOT.Var.ConvexLE μ ν) (h : ℝ → ℝ) (hd : Differentiable ℝ h)
    (hconv : StrictConvexOn ℝ Set.univ (deriv h))
    (hint : MartOT.Var.SuffIntegrable μ ν (fun x y => h (y - x))) (π : Measure (ℝ × ℝ))
    (hπ : MartOT.Var.IsOptimal (fun x y => h (y - x)) μ ν π) (hfin : MartOT.Var.cost (fun x y => h (y - x)) π < ⊤) :
    MartOT.Var.IsLeftMonotone π := by sorry

end MartOT.Opt
