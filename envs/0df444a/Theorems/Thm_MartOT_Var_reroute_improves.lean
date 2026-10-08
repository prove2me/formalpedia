-- Prove2me | Theorems.Thm_MartOT_Var_reroute_improves
-- name    : MartOT.Var.reroute_improves
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:11:24.998749+00:00
-- url     : https://prove2.me/theorems/44817a52-49c5-4802-bd55-1351b163b2af
-- title:
--   Proof of Lemma 1.11, p. 18 — replacing ω ≤ π by a cheaper competitor ω′ gives a cheaper martingale plan π − ω + ω′
-- statement:
--   Let $\mu,\nu$ be probability measures on $\mathbb R$ in convex order, $c:\mathbb R^2\to\mathbb R$ a Borel cost satisfying the sufficient integrability condition, and $\pi\in\Pi_M(\mu,\nu)$ a martingale transport plan with finite cost $\int c\,d\pi<+\infty$. Let $\omega$ be a finite measure with $\omega\le\pi$, and let $\omega'$ be a competitor of $\omega$ with
--   $$\int c\,d\omega'<\int c\,d\omega .$$
--   Then $\pi-\omega+\omega'\in\Pi_M(\mu,\nu)$ and
--   $$\int c\,d(\pi-\omega+\omega')<\int c\,d\pi .$$
--
--   This is the step by which, in the proof of the variational lemma, an improvable piece $\omega$ of an optimal plan contradicts its optimality.
--
--   **Formalization Note** $\pi-\omega$ is the difference of measures, well defined since $\omega\le\pi$ and $\omega$ is finite. Integrability of $c$ against $\omega$ and $\omega'$ is not assumed: it follows from $\omega\le\pi$, finite cost of $\pi$, the sufficient integrability condition and the fact that $\omega'$ has the marginals of $\omega$. Costs are extended-real integrals.
-- source:
--   arXiv:1208.1509v2, §3, proof of Lemma 1.11, p. 18 ("If such a measure ω′ exists then the measure π − ω + ω′ is a martingale transport plan …")

import Mathlib
import Definitions.Def_MartOT_Var_Setting

namespace MartOT.Var

open MeasureTheory

theorem reroute_improves (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : ConvexLE μ ν) (c : ℝ → ℝ → ℝ) (hc : Measurable (Function.uncurry c))
    (hint : SuffIntegrable μ ν c) (π : Measure (ℝ × ℝ)) (hπ : IsMartingalePlan μ ν π)
    (hfin : cost c π < ⊤) (ω ω' : Measure (ℝ × ℝ)) [IsFiniteMeasure ω] (hωπ : ω ≤ π)
    (hcomp : IsCompetitor ω ω') (hlt : cost c ω' < cost c ω) :
    IsMartingalePlan μ ν (π - ω + ω') ∧ cost c (π - ω + ω') < cost c π := by sorry

end MartOT.Var
