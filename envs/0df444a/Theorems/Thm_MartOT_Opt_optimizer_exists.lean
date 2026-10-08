-- Prove2me | Theorems.Thm_MartOT_Opt_optimizer_exists
-- name    : MartOT.Opt.optimizer_exists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:19:55.828553+00:00
-- url     : https://prove2.me/theorems/721cbd32-da0c-49cd-ac49-1b48d0045b15
-- title:
--   §2.1, pp. 10–11 — for a lower semicontinuous cost the martingale transport problem (2) attains its infimum when Π_M(µ, ν) ≠ ∅
-- statement:
--   Let $\mu,\nu$ be probability measures on $\mathbb R$ with finite first moment and let $c:\mathbb R^2\to\mathbb R$ be a lower semicontinuous cost function satisfying the sufficient integrability condition: $c(x,y)\ge a(x)+b(y)$ for all $x,y$, with $a\in L^1(\mu)$ and $b\in L^1(\nu)$. Assume that the set $\Pi_M(\mu,\nu)$ of martingale transport plans from $\mu$ to $\nu$ is nonempty. Then the martingale optimal transport problem
--
--   $$C_M(\mu,\nu)=\inf_{\pi\in\Pi_M(\mu,\nu)}\int c\,d\pi$$
--
--   has a minimizer: there is $\pi^\ast\in\Pi_M(\mu,\nu)$ with $\int c\,d\pi^\ast\le\int c\,d\pi$ for every $\pi\in\Pi_M(\mu,\nu)$.
--
--   This is the existence half of "$\pi_{lc}$ is the unique optimizer": once some optimizer exists, the structural results of the paper identify it.
--
--   **Formalization Note** Costs $\int c\,d\pi$ take values in $(-\infty,+\infty]$ and are computed in the extended reals. No finiteness of $C_M(\mu,\nu)$ is assumed: if every plan has infinite cost, every plan is a minimizer, which the statement allows. Lower semicontinuity is with respect to the usual topology of $\mathbb R^2$. The paper states the attainment for $\mu,\nu$ in $\mathcal M$, the finite measures with finite first moment (§2.1, p. 10); the statement keeps the finite first moments as hypotheses and specializes the mass to $1$, the case the goal theorem needs.
-- source:
--   arXiv:1208.1509v2, §2.1, pp. 10–11 (unnumbered: "the value of the minimization problem (2) is attained provided that the set Π_M(µ,ν) is nonempty")

import Mathlib
import Definitions.Def_MartOT_Var_Setting

namespace MartOT.Opt

open MeasureTheory

theorem optimizer_exists (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : MartOT.Var.InM μ) (hν : MartOT.Var.InM ν) (c : ℝ → ℝ → ℝ) (hc : LowerSemicontinuous (Function.uncurry c))
    (hint : MartOT.Var.SuffIntegrable μ ν c) (hne : ∃ π : Measure (ℝ × ℝ), MartOT.Var.IsMartingalePlan μ ν π) :
    ∃ π : Measure (ℝ × ℝ), MartOT.Var.IsOptimal c μ ν π := by sorry

end MartOT.Opt
