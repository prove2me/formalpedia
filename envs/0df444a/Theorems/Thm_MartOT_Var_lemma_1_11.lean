-- Prove2me | Theorems.Thm_MartOT_Var_lemma_1_11
-- name    : MartOT.Var.lemma_1_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:11:33.292979+00:00
-- url     : https://prove2.me/theorems/5c84a1fc-3e23-481a-8140-79f402b28241
-- title:
--   Lemma 1.11, p. 8 — variational lemma: an optimal martingale plan lives on a Borel Γ where no finitely supported α has a cheaper competitor
-- statement:
--   Let $\mu,\nu$ be probability measures on $\mathbb R$ in convex order, and let $c:\mathbb R^2\to\mathbb R$ be a Borel measurable cost function satisfying the sufficient integrability condition $c(x,y)\ge a(x)+b(y)$ with $a\in L^1(\mu)$, $b\in L^1(\nu)$. Let $\pi\in\Pi_M(\mu,\nu)$ be an optimal martingale transport plan with finite cost, $\int c\,d\pi<+\infty$.
--
--   Then there is a Borel set $\Gamma\subseteq\mathbb R^2$ with $\pi(\Gamma)=1$ such that: whenever $\alpha$ is a finite measure on $\mathbb R\times\mathbb R$ with finite support $\operatorname{spt}\alpha\subseteq\Gamma$,
--   $$\int c\,d\alpha\le\int c\,d\alpha'\qquad\text{for every competitor }\alpha'\text{ of }\alpha,$$
--   where a competitor has the same marginals as $\alpha$ and the same conditional barycentres $\int y\,d\alpha_x(y)$.
--
--   The set $\Gamma$ is chosen once, before $\alpha$. The lemma is the martingale counterpart of $c$-cyclical monotonicity in classical optimal transport: it turns global optimality of $\pi$ into a pointwise condition on finitely many points of its support, and it is the tool by which the paper derives the structure of optimal plans (left-monotonicity, the cardinality bounds of Section 7).
--
--   **Formalization Note** "Leads to finite costs" is $E_\pi[c]<+\infty$ in the extended reals; without it every plan could have cost $+\infty$ and optimality would be empty. $\pi(\Gamma)=1$ is written $\pi(\Gamma^c)=0$ ($\pi$ is a probability measure). A finitely supported finite measure is written $\sum_{s\in S}w_s\delta_s$ with $S$ a finite set and $w_s\ge0$; this covers every such $\alpha$ (take $S=\operatorname{spt}\alpha$), and zero weights add nothing. The page says "a measure"; masses are taken finite. The competitor $\alpha'$ ranges over all measures.
-- source:
--   arXiv:1208.1509v2, Lemma 1.11, p. 8 (proof §3, pp. 16–19)

import Mathlib
import Definitions.Def_MartOT_Var_Setting

namespace MartOT.Var

open MeasureTheory

theorem lemma_1_11 (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : ConvexLE μ ν) (c : ℝ → ℝ → ℝ) (hc : Measurable (Function.uncurry c))
    (hint : SuffIntegrable μ ν c) (π : Measure (ℝ × ℝ)) (hπ : IsOptimal c μ ν π)
    (hfin : cost c π < ⊤) :
    ∃ Γ : Set (ℝ × ℝ), MeasurableSet Γ ∧ π Γᶜ = 0 ∧
      ∀ (S : Finset (ℝ × ℝ)) (w : ℝ × ℝ → NNReal), (↑S : Set (ℝ × ℝ)) ⊆ Γ →
        ∀ α' : Measure (ℝ × ℝ),
          IsCompetitor (∑ p ∈ S, (w p : ENNReal) • Measure.dirac p) α' →
          cost c (∑ p ∈ S, (w p : ENNReal) • Measure.dirac p) ≤ cost c α' := by sorry

end MartOT.Var
