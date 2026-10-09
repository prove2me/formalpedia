-- Prove2me | Theorems.Thm_LookbackMOT_HL_lemma_3_1
-- name    : LookbackMOT.HL.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:33:46.350314+00:00
-- url     : https://prove2.me/theorems/2cfd3917-13f0-4a22-9c7b-48341be89d6a
-- title:
--   Lemma 3.1, p. 14 — for λ ∈ Λ̂^μ_0 and ψ ∈ Ψ^λ, the stopping value u^λ is dominated by v^ψ on Δ
-- statement:
--   Let $B$ be an $(\mathcal F_t)$-Brownian motion, $X^x=x+B$, and $\mathcal T_\infty$ the stopping times $\tau$ for which $(X_{t\wedge\tau})_{t\ge0}$ is a uniformly integrable martingale. Let $\mu$ be an integrable probability measure on $\mathbb R$ with mean $X_0$, let $g:\mathbb R\to\mathbb R_+$ be $C^1$ and nondecreasing, and let $\lambda\in\hat\Lambda^\mu_0$ (a convex element of $\Lambda^\mu_0$) and $\psi\in\Psi^\lambda$. Then for every $(x,m)$ with $x\le m$,
--   $$u^\lambda(x,m)=\sup_{\tau\in\mathcal T_\infty}\mathbb E\Big[g\big(m\vee\max_{t\le\tau}X^x_t\big)-\lambda(X^x_\tau)\Big]\ \le\ v^\psi(x,m),$$
--   where $v^\psi$ is Peskir's candidate (3.18).
--
--   It is the verification step of the upper bound: every relaxed solution $\psi$ of the free-boundary ODE gives an upper bound for the value of the stopping problem. It extends the easy half of Peskir's maximality principle to nonsmooth $\lambda$.
--
--   **Formalization Note** Expectations are $\mathbb E[\varphi^+]-\mathbb E[\varphi^-]$ in the extended reals, so the supremum is in $[-\infty,+\infty]$. The setting binders, the integrability and mean of $\mu$ and the measurability of $\lambda$ are those of the Setting file; $\lambda''$ is supplied as a measure satisfying its defining identity.
-- source:
--   Galichon, Henry-Labordère & Touzi, A stochastic control approach to no-arbitrage bounds given marginals, with an application to lookback options, arXiv:1401.3921v1, p. 14, Lemma 3.1

import Mathlib
import Definitions.Def_LookbackMOT_HL_Setting

open MeasureTheory ProbabilityTheory LookbackMOT.HL
open scoped NNReal ENNReal

namespace LookbackMOT.HL

theorem lemma_3_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (B : ℝ≥0 → Ω → ℝ) (hB : IsFBrownian P ℱ B)
    (X₀ : ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ1 : Integrable id μ)
    (hmean : ∫ x, x ∂μ = X₀)
    (g : ℝ → ℝ) (hg0 : ∀ x, 0 ≤ g x) (hgC1 : ContDiff ℝ 1 g) (hgmono : Monotone g)
    (lam : ℝ → ℝ) (hlam : InLambda0Hat P ℱ B X₀ μ lam)
    (ν₂ : Measure ℝ) (hν₂ : IsSecondDerivMeasure lam ν₂) (ψ : ℝ → ℝ) (hψ : InPsi g lam ν₂ ψ) :
    ∀ x m : ℝ, x ≤ m → stopValue P ℱ B g lam x m ≤ ((vpsi g lam ψ x m : ℝ) : EReal) := by sorry

end LookbackMOT.HL
