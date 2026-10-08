-- Prove2me | Theorems.Thm_MartOT_HN_optimizer_exists
-- name    : MartOT.HN.optimizer_exists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:19:06.896175+00:00
-- url     : https://prove2.me/theorems/9757eb3b-b747-428c-b53a-fe8ad56757b2
-- title:
--   §2.1, pp. 10–11 — for a lower semicontinuous cost with the sufficient integrability condition, an optimal martingale plan exists if Π_M(µ, ν) ≠ ∅
-- statement:
--   Let $\mu,\nu$ be finite measures on $\mathbb R$ with finite first moments, and let $c:\mathbb R^2\to\mathbb R$ be lower semicontinuous and satisfy the sufficient integrability condition $c(x,y)\ge a(x)+b(y)$ with $a\in L^1(\mu)$, $b\in L^1(\nu)$. If the set $\Pi_M(\mu,\nu)$ of martingale transport plans is nonempty, then the minimization problem
--
--   $$C_M(\mu,\nu)=\inf\Big\{\int c\,d\pi:\ \pi\in\Pi_M(\mu,\nu)\Big\}$$
--
--   is attained: some $\pi\in\Pi_M(\mu,\nu)$ satisfies $\int c\,d\pi\le\int c\,d\pi'$ for every $\pi'\in\Pi_M(\mu,\nu)$.
--
--   This is the existence half of the martingale transport problem; for the Hobson–Neuberger cost $c(x,y)=-|y-x|$ it provides the plan whose structure and uniqueness Theorem 7.3 describes.
--
--   **Formalization Note** Section 2.1 extends the setting to $\mu,\nu\in\mathcal M$, finite measures with finite first moments; this claim does not require probability measures. Costs take values in $(-\infty,+\infty]$ (extended reals), so the infimum is attained even when every plan has infinite cost.
-- source:
--   arXiv:1208.1509v2, §2.1, pp. 10–11 (attainment of (2): lower semicontinuity of π ↦ ∫ c dπ, p. 10; compactness of Π_M(µ, ν), p. 11)

import Mathlib
import Definitions.Def_MartOT_Var_Setting

namespace MartOT.HN

open MeasureTheory

theorem optimizer_exists (μ ν : Measure ℝ) (hμ : MartOT.Var.InM μ) (hν : MartOT.Var.InM ν)
    (c : ℝ → ℝ → ℝ) (hc : LowerSemicontinuous (Function.uncurry c))
    (hint : MartOT.Var.SuffIntegrable μ ν c) (hne : ∃ π, MartOT.Var.IsMartingalePlan μ ν π) :
    ∃ π, MartOT.Var.IsOptimal c μ ν π := by sorry

end MartOT.HN
