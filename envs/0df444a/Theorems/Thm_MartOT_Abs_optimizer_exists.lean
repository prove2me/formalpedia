-- Prove2me | Theorems.Thm_MartOT_Abs_optimizer_exists
-- name    : MartOT.Abs.optimizer_exists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:19:15.513716+00:00
-- url     : https://prove2.me/theorems/05c73824-bf11-4304-a4b4-d2530362aafc
-- title:
--   §2.1, pp. 10–11 — for a lower semicontinuous cost with the sufficient integrability condition, an optimal martingale plan exists if Π_M(µ, ν) ≠ ∅
-- statement:
--   Let $\mu,\nu$ be finite Borel measures on $\mathbb R$ with finite first moments, and let $c:\mathbb R^2\to\mathbb R$ be lower semicontinuous and satisfy the sufficient integrability condition $c(x,y)\ge a(x)+b(y)$ with $a\in L^1(\mu)$, $b\in L^1(\nu)$. If the set $\Pi_M(\mu,\nu)$ of martingale transport plans is nonempty, then the minimization problem
--
--   $$C_M(\mu,\nu)=\inf\Big\{\int c\,d\pi:\ \pi\in\Pi_M(\mu,\nu)\Big\}$$
--
--   is attained: some $\pi\in\Pi_M(\mu,\nu)$ satisfies $\int c\,d\pi\le\int c\,d\pi'$ for every $\pi'\in\Pi_M(\mu,\nu)$.
--
--   This is the existence half of the martingale transport problem. For the cost $c(x,y)=|y-x|$, which is continuous and nonnegative (the sufficient integrability condition holds with $a=b=0$), it provides the plan whose uniqueness and structure Theorem 7.4 describes.
--
--   **Formalization Note** The finite mass and first moment hypotheses are the class $\mathcal M$ of §2.1; the measures need not have unit mass. Costs take values in $(-\infty,+\infty]$ (extended reals) under the stated sufficient integrability condition, so the minimum is meaningful even if every plan has infinite cost.
-- source:
--   arXiv:1208.1509v2, §2.1, pp. 10–11 (attainment of (2): lower semicontinuity of π ↦ ∫ c dπ, p. 10; compactness of Π_M(µ, ν), p. 11)

import Mathlib
import Definitions.Def_MartOT_Var_Setting

namespace MartOT.Abs

open MeasureTheory

theorem optimizer_exists (μ ν : Measure ℝ) (hμ : MartOT.Var.InM μ) (hν : MartOT.Var.InM ν)
    (c : ℝ → ℝ → ℝ) (hc : LowerSemicontinuous (Function.uncurry c))
    (hint : MartOT.Var.SuffIntegrable μ ν c) (hne : ∃ π, MartOT.Var.IsMartingalePlan μ ν π) :
    ∃ π, MartOT.Var.IsOptimal c μ ν π := by sorry

end MartOT.Abs
