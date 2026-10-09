-- Prove2me | Theorems.Thm_LookbackMOT_HL_lemma_3_3_step_3
-- name    : LookbackMOT.HL.lemma_3_3_step_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:33:56.732678+00:00
-- url     : https://prove2.me/theorems/4f4d04a7-4a5e-484e-867f-372da3a0b538
-- title:
--   Proof of Lemma 3.3, step (3), p. 18 — integration by parts: g(X₀) + ∫_{X₀}^∞ μ^HL([y, ∞)) g′(y) dy = μ^HL(g)
-- statement:
--   Let $\mu$ be an integrable probability measure on $\mathbb R$ with mean $X_0$ and Hardy–Littlewood transform $\mu^{HL}$, and let $g:\mathbb R\to\mathbb R_+$ be $C^1$, nondecreasing and $\mu^{HL}$-integrable. Then
--   $$g(X_0)+\int_{X_0}^{\infty}\mu^{HL}([y,\infty))\,g'(y)\,dy=\int g\,d\mu^{HL}=\mu^{HL}(g).$$
--
--   This is the last line of the upper bound: the value $g(X_0)+\int c(\beta(x))/(x-\beta(x))\,g'(x)\,dx$ produced by the pointwise minimization is the price $\mu^{HL}(g)$ of the payoff under the Hardy–Littlewood transform.
--
--   **Formalization Note** The integral runs over $[X_0,\infty)$: below $X_0$ the integrand of (3.26) is $0$ by (3.27), and $\mu^{HL}([y,\infty))=1$ for $y\le X_0$, so integrating over all of $\mathbb R$ would add $g(X_0)-g(-\infty)$. The page prints $\int\mu^{HL}([y,\infty))g'(x)\,dx$, with mismatched variables; the integration variable is $y$.
-- source:
--   Galichon, Henry-Labordère & Touzi, A stochastic control approach to no-arbitrage bounds given marginals, with an application to lookback options, arXiv:1401.3921v1, p. 18, step (3) of the proof of Lemma 3.3

import Mathlib
import Definitions.Def_LookbackMOT_HL_Setting

open MeasureTheory ProbabilityTheory LookbackMOT.HL
open scoped NNReal ENNReal

namespace LookbackMOT.HL

theorem lemma_3_3_step_3 (X₀ : ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ1 : Integrable id μ)
    (hmean : ∫ x, x ∂μ = X₀)
    (g : ℝ → ℝ) (hg0 : ∀ x, 0 ≤ g x) (hgC1 : ContDiff ℝ 1 g) (hgmono : Monotone g)
    (ν : Measure ℝ) (hν : IsHLTransform μ ν) (hνg : Integrable g ν) :
    g X₀ + ∫ y in Set.Ici X₀, (ν (Set.Ici y)).toReal * deriv g y = ∫ x, g x ∂ν := by sorry

end LookbackMOT.HL
