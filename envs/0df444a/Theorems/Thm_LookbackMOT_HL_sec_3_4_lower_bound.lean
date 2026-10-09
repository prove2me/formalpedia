-- Prove2me | Theorems.Thm_LookbackMOT_HL_sec_3_4_lower_bound
-- name    : LookbackMOT.HL.sec_3_4_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:34:28.104093+00:00
-- url     : https://prove2.me/theorems/8717c810-9b53-4dab-84ee-8217f4a08ed5
-- title:
--   §3.4, p. 18 — lower bound: inf_{λ∈Λ^μ_0} {μ(λ) + u^λ(X₀, X₀)} ≥ μ^HL(g)
-- statement:
--   Let $B$ be an $(\mathcal F_t)$-Brownian motion and $X=X_0+B$, let $\mu$ be an integrable probability measure on $\mathbb R$ with mean $X_0$ and Hardy–Littlewood transform $\mu^{HL}$, and let $g:\mathbb R\to\mathbb R_+$ be $C^1$ and nondecreasing with
--   $$\sup_{\tau\in\mathcal T_\infty}\mathbb E\big[g(X^*_\tau)\big]<\infty\qquad\text{and}\qquad \mu^{HL}(g)<\infty .$$
--   Then
--   $$\inf_{\lambda\in\Lambda^\mu_0}\big\{\mu(\lambda)+u^\lambda(X_0,X_0)\big\}\ \ge\ \mu^{HL}(g).$$
--
--   This is the lower half of Theorem 3.1: no static position in European options combined with optimal stopping can do better than the Hardy–Littlewood price.
--
--   **Formalization Note** The first hypothesis is the theorem's $\sup_{\mathbb P\in\mathcal P_\infty}\mathbb E^{\mathbb P}[\xi^+]<\infty$ translated through Proposition 3.1 with $\lambda=0$ (here $\xi=g(X^*)\ge0$, so $\xi^+=\xi$). $\mu^{HL}(g)<\infty$ is integrability of $g$ under $\mu^{HL}$, and $\mu^{HL}(g)$ is the real integral.
-- source:
--   Galichon, Henry-Labordère & Touzi, A stochastic control approach to no-arbitrage bounds given marginals, with an application to lookback options, arXiv:1401.3921v1, p. 18, §3.4

import Mathlib
import Definitions.Def_LookbackMOT_HL_Setting

open MeasureTheory ProbabilityTheory LookbackMOT.HL
open scoped NNReal ENNReal

namespace LookbackMOT.HL

theorem sec_3_4_lower_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (B : ℝ≥0 → Ω → ℝ) (hB : IsFBrownian P ℱ B)
    (X₀ : ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ1 : Integrable id μ)
    (hmean : ∫ x, x ∂μ = X₀)
    (g : ℝ → ℝ) (hg0 : ∀ x, 0 ≤ g x) (hgC1 : ContDiff ℝ 1 g) (hgmono : Monotone g)
    (hξ : (⨆ τ : Ω → WithTop ℝ≥0, ⨆ (_ : IsUIStop P ℱ (shift X₀ B) τ),
      ∫⁻ ω, ENNReal.ofReal (g (runMaxUpTo (shift X₀ B) τ ω)) ∂P) < ⊤)
    (ν : Measure ℝ) (hν : IsHLTransform μ ν) (hνg : Integrable g ν) :
    ((∫ x, g x ∂ν : ℝ) : EReal) ≤ U P ℱ B X₀ μ g := by sorry

end LookbackMOT.HL
