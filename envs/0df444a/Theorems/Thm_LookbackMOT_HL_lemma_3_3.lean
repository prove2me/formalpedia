-- Prove2me | Theorems.Thm_LookbackMOT_HL_lemma_3_3
-- name    : LookbackMOT.HL.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:34:09.078072+00:00
-- url     : https://prove2.me/theorems/45406126-78d3-4f31-a717-7e31e2b55519
-- title:
--   Lemma 3.3, p. 16 — upper bound: inf_{λ∈Λ^μ_0} {μ(λ) + u^λ(X₀, X₀)} ≤ μ^HL(g)
-- statement:
--   Let $B$ be an $(\mathcal F_t)$-Brownian motion and $X=X_0+B$, let $\mu$ be an integrable probability measure on $\mathbb R$ with mean $X_0$ and Hardy–Littlewood transform $\mu^{HL}$, and let $g:\mathbb R\to\mathbb R_+$ be a nondecreasing $C^1$ payoff function. Then
--   $$U^\mu(\xi)=\inf_{\lambda\in\Lambda^\mu_0}\big\{\mu(\lambda)+u^\lambda(X_0,X_0)\big\}\ \le\ \mu^{HL}(g)=\int g\,d\mu^{HL}.$$
--
--   This is the upper half of Theorem 3.1: the robust superhedging cost of the lookback payoff $g(X^*_T)$, in its reduced form (3.7), is at most the price of $g$ under the Hardy–Littlewood transform.
--
--   **Formalization Note** No integrability of $g$ under $\mu^{HL}$ is assumed: the right side is $\int g\,d\mu^{HL}\in[0,\infty]$ and both sides are compared in the extended reals.
-- source:
--   Galichon, Henry-Labordère & Touzi, A stochastic control approach to no-arbitrage bounds given marginals, with an application to lookback options, arXiv:1401.3921v1, p. 16, Lemma 3.3

import Mathlib
import Definitions.Def_LookbackMOT_HL_Setting

open MeasureTheory ProbabilityTheory LookbackMOT.HL
open scoped NNReal ENNReal

namespace LookbackMOT.HL

theorem lemma_3_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (B : ℝ≥0 → Ω → ℝ) (hB : IsFBrownian P ℱ B)
    (X₀ : ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ1 : Integrable id μ)
    (hmean : ∫ x, x ∂μ = X₀)
    (g : ℝ → ℝ) (hg0 : ∀ x, 0 ≤ g x) (hgC1 : ContDiff ℝ 1 g) (hgmono : Monotone g)
    (ν : Measure ℝ) (hν : IsHLTransform μ ν) :
    U P ℱ B X₀ μ g ≤ ((∫⁻ x, ENNReal.ofReal (g x) ∂ν : ℝ≥0∞) : EReal) := by sorry

end LookbackMOT.HL
