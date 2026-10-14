-- Prove2me | Theorems.Thm_MLLangevin_General_proposition_3_3
-- name    : MLLangevin.General.proposition_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:10:17.570292+00:00
-- url     : https://prove2.me/theorems/ba21f6af-517e-4820-9a07-9674ef78a321
-- title:
--   Proposition 3.3, p. 25 — Var(𝒴) ≤ 𝔠_u[f]₁²(αT₀)⁻¹(c₄² + max(c₂², c₂c₄)γ₀^𝔞log(γ₀⁻¹)((𝔞 − 1)⁻² ∧ R²)), 𝔠_u universal
-- statement:
--   There is a universal constant $\mathfrak c_u$ such that the following holds. Let $B^{(0)},B^{(1)},\dots$ be independent standard $d$-dimensional Brownian motions, $b,\sigma,f$ Lipschitz. Assume $(\mathbf H_1)$, $(\mathbf H_2)$ and $(\mathbf H_4)$ (for every level's Brownian motion) for some $\mathfrak a\in[1,2]$, $\alpha>0$, $\eta_0\in(0,1/2]$ with $\alpha\eta_0\le1$, and $x_0\in\mathbb R^d$. Let $\gamma_0\in(0,\eta_0]$, $R\ge1$, $\gamma_r=\gamma_02^{-r}$ and $T_r=T_02^{-\frac{1+\mathfrak a}2r}$ with $T_0>0$, and let $\tau>0$ with $\tau\le T_R/2$. Then
--   $$\operatorname{Var}\big(\mathcal Y(R,(\gamma_r)_r,\tau,(T_r)_r,f)\big)\le\mathfrak c_u\frac{[f]_1^2}{\alpha T_0}\Big(c_4^2+\max(c_2^2,c_2c_4)\gamma_0^{\mathfrak a}\log(\gamma_0^{-1})\big((\mathfrak a-1)^{-2}\wedge R^2\big)\Big),$$
--   with $(\mathfrak a-1)^{-2}\wedge R^2=R^2$ when $\mathfrak a=1$.
--
--   This is the variance half of the bias–variance decomposition of Proposition 3.1.
--
--   **Formalization Note.** $\mathfrak c_u$ is quantified before everything else (dimension, probability space, coefficients, $f$, constants and parameters), so it is universal. Added to the page: $\eta_0\le1/2$, the standing range of Theorem 2.1 and Proposition 3.1 (without an upper bound on $\eta_0$, $\log(\gamma_0^{-1})$ can be negative and the bound fails); $\gamma_0>0$ (the page writes $\gamma_0\in[0,\eta_0]$, but $\log(\gamma_0^{-1})$ needs $\gamma_0>0$); $R\ge1$ ($R\in\mathbb N^*$, §2.2). The measures $\pi^\gamma$ enter only through $(\mathbf H_1)$.
-- source:
--   Egéa–Panloup, arXiv:2109.07753v2, Proposition 3.3 and Remark 3.3, p. 25 (proof pp. 25–26)

import Mathlib
import Definitions.Def_MLLangevin_General_Setting

namespace MLLangevin.General

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

theorem proposition_3_3 :
    ∃ cu : ℝ, ∀ {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (B : ℕ → ℝ≥0 → Ω → Rd d), (∀ r, EthierKurtz.IsStandardBrownian P (B r)) →
      iIndepFun (fun r ω => fun t => B r t ω) P →
      ∀ (b : Rd d → Rd d) (σ : Rd d → (Rd d →L[ℝ] Rd d)),
      (∃ K, LipschitzWith K b) → (∃ K, LipschitzWith K σ) →
      ∀ (f : Rd d → ℝ), (∃ K, LipschitzWith K f) →
      ∀ (πγ : ℝ → Measure (Rd d)) (α 𝔞 η₀ : ℝ) (x₀ : Rd d) (c₁ : Rd d → ℝ) (c₂ c₄ : ℝ),
      0 < α → 1 ≤ 𝔞 → 𝔞 ≤ 2 → 0 < η₀ → η₀ ≤ 1 / 2 → α * η₀ ≤ 1 →
      (∀ r, H1 P b σ (B r) f πγ α η₀ c₁) → (∀ r, H2 P b σ (B r) x₀ η₀ 𝔞 c₂) →
      (∀ r, H4 P b σ (B r) x₀ η₀ c₁ c₄) →
      ∀ (γ₀ : ℝ) (R : ℕ) (τ T₀ : ℝ), 0 < γ₀ → γ₀ ≤ η₀ → 1 ≤ R → 0 < T₀ → 0 < τ →
      τ ≤ geomHorizon T₀ 𝔞 R / 2 →
      evariance (estimator b σ x₀ γ₀ R τ (geomHorizon T₀ 𝔞) B f) P
        ≤ ENNReal.ofReal (cu * lipConst f ^ 2 / (α * T₀)
            * (c₄ ^ 2 + max (c₂ ^ 2) (c₂ * c₄) * γ₀ ^ 𝔞 * Real.log γ₀⁻¹ * minTerm 𝔞 R)) := by sorry

end MLLangevin.General
