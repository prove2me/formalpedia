-- Prove2me | Theorems.Thm_LookbackMOT_HL_lemma_3_2_step_1
-- name    : LookbackMOT.HL.lemma_3_2_step_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:34:04.851255+00:00
-- url     : https://prove2.me/theorems/8c6b9ec8-ab5b-4a0f-8229-4d6c0cbd1541
-- title:
--   Proof of Lemma 3.2, step (1), p. 16 — μ(λ) − λ(X₀) = ∫ (c − c₀)(y) λ″(dy) for convex λ ∈ L¹(μ)
-- statement:
--   Let $\mu$ be an integrable probability measure on $\mathbb R$ with mean $X_0$, with call price $c(y)=\int(x-y)^+\mu(dx)$, and let $c_0(y)=(X_0-y)^+$. Let $\lambda:\mathbb R\to\mathbb R$ be convex and $\mu$-integrable, with second-derivative measure $\lambda''$. Then $\mu(\lambda)-\lambda(X_0)\ge0$ and
--   $$\mu(\lambda)-\lambda(X_0)=\int (c-c_0)(y)\,\lambda''(dy).$$
--
--   This identity converts the static part $\mu(\lambda)$ of the dual objective into an integral against $\lambda''$; combined with the ODE (3.21) it turns the upper bound of Lemma 3.1 into the explicit bound of Lemma 3.2, and in step (2) of Lemma 3.3 it reduces $\lambda^*\in\mathbb L^1(\mu)$ to $\int c\,d(\lambda^*)''<\infty$.
--
--   **Formalization Note** The identity is stated in $[0,\infty]$: the left side is nonnegative (Jensen) and the integrand $c-c_0$ is nonnegative, so no information is lost. The paper's hypothesis $\lambda\in\hat\Lambda^\mu_0$ is replaced by "convex and $\mu$-integrable", the only parts of it the step uses; the stopping-time condition of $\Lambda^\mu_0$ is dropped, which makes the statement more general. The mean condition $\int x\,\mu(dx)=X_0$ (p. 7) is assumed.
-- source:
--   Galichon, Henry-Labordère & Touzi, A stochastic control approach to no-arbitrage bounds given marginals, with an application to lookback options, arXiv:1401.3921v1, p. 16, step (1) of the proof of Lemma 3.2

import Mathlib
import Definitions.Def_LookbackMOT_HL_Setting

open MeasureTheory ProbabilityTheory LookbackMOT.HL
open scoped NNReal ENNReal

namespace LookbackMOT.HL

theorem lemma_3_2_step_1 (X₀ : ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ1 : Integrable id μ)
    (hmean : ∫ x, x ∂μ = X₀)
    (lam : ℝ → ℝ) (hconv : ConvexOn ℝ Set.univ lam) (hint : Integrable lam μ)
    (ν₂ : Measure ℝ) (hν₂ : IsSecondDerivMeasure lam ν₂) :
    0 ≤ (∫ x, lam x ∂μ) - lam X₀ ∧
      ENNReal.ofReal ((∫ x, lam x ∂μ) - lam X₀) =
        ∫⁻ y, ENNReal.ofReal (callPrice μ y - c0 X₀ y) ∂ν₂ := by sorry

end LookbackMOT.HL
