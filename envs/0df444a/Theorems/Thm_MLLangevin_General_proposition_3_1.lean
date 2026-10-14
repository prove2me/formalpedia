-- Prove2me | Theorems.Thm_MLLangevin_General_proposition_3_1
-- name    : MLLangevin.General.proposition_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:10:17.753935+00:00
-- url     : https://prove2.me/theorems/e5985448-0cbe-4ad5-a1bb-be284afb0664
-- title:
--   Proposition 3.1, pp. 20–21 — ‖𝒴 − π(f)‖₂² ≤ [f]₁²(variance bound + (c₃γ_R^δ + 𝔠_uc₁(x₀)e^{−ατ}2^{((1+𝔞)/2)R}/(αT₀))²), 𝔠_u universal, and (28)
-- statement:
--   There is a universal constant $\mathfrak c_u$ such that the following holds. Let $B^{(0)},B^{(1)},\dots$ be independent standard $d$-dimensional Brownian motions, $b,\sigma,f$ Lipschitz, $\pi$ a probability measure and $(\pi^\gamma)_{\gamma\in(0,\eta_0]}$ probability measures, $f$ integrable for each of them. Assume $(\mathbf H_1)$–$(\mathbf H_4)$ (with $(\mathbf H_1)$, $(\mathbf H_2)$, $(\mathbf H_4)$ for every level's Brownian motion) for some $\mathfrak a\in[1,2]$, $\alpha>0$, $\eta_0\in(0,1/2]$ and $x_0\in\mathbb R^d$. Let $\gamma_0\in(0,\eta_0]$ with $\alpha\gamma_0\le1$, $R\ge1$, $T_0>0$, $\gamma_r=\gamma_02^{-r}$, $T_r=T_02^{-\frac{1+\mathfrak a}2r}$, and $\tau\ge0$ with $\tau\le T_R/2$. Then, with $\mathcal Y=\mathcal Y(R,(\gamma_r)_r,\tau,(T_r)_r,f)$,
--   $$\|\mathcal Y-\pi(f)\|_2^2\le[f]_1^2\left[\frac{\mathfrak c_u}{\alpha T_0}\Big(c_4^2+\max(c_2^2,c_2c_4)\gamma_0^{\mathfrak a}\log(\gamma_0^{-1})\big((\mathfrak a-1)^{-2}\wedge R^2\big)\Big)+\Big(c_3\gamma_R^\delta+\frac{\mathfrak c_uc_1(x_0)}{\alpha T_0}e^{-\alpha\tau}2^{\frac{1+\mathfrak a}2R}\Big)^2\right],$$
--   and the complexity satisfies (28):
--   $$\mathcal C(\mathcal Y)\le\begin{cases}\frac{T_0}{\gamma_0}\big(1+\frac32(2^{\frac{\mathfrak a-1}2}-1)^{-1}\big)&\mathfrak a>1,\\ \frac{T_0(1+\frac32R)}{\gamma_0}&\mathfrak a=1.\end{cases}$$
--
--   This is the non-asymptotic error bound behind Theorem 2.1: the first bracket is the variance (Proposition 3.3), the square the squared bias (Proposition 3.2).
--
--   **Formalization Note.** $\mathfrak c_u$ is quantified first, before every datum. The page divides by $[f]_1^2$ for a non-constant $f$; the Lean multiplies out, which is the same statement for non-constant $f$ and also covers constant $f$ (both sides are then $0$). $\|\cdot\|_2^2$ is `eLpNorm · 2 P ^ 2` in $[0,\infty]$. Added: $R\ge1$ ($R\in\mathbb N^*$, §2.2) and $\eta_0>0$ (the page writes $\eta_0\in[0,1/2]$; $\eta_0$ is positive by the standing assumption of p. 6).
-- source:
--   Egéa–Panloup, arXiv:2109.07753v2, Proposition 3.1 and (28), pp. 20–21

import Mathlib
import Definitions.Def_MLLangevin_General_Setting

namespace MLLangevin.General

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

theorem proposition_3_1 :
    ∃ cu : ℝ, ∀ {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (B : ℕ → ℝ≥0 → Ω → Rd d), (∀ r, EthierKurtz.IsStandardBrownian P (B r)) →
      iIndepFun (fun r ω => fun t => B r t ω) P →
      ∀ (b : Rd d → Rd d) (σ : Rd d → (Rd d →L[ℝ] Rd d)),
      (∃ K, LipschitzWith K b) → (∃ K, LipschitzWith K σ) →
      ∀ (f : Rd d → ℝ), (∃ K, LipschitzWith K f) →
      ∀ (π : Measure (Rd d)) [IsProbabilityMeasure π] (πγ : ℝ → Measure (Rd d))
        (α 𝔞 δ η₀ : ℝ) (x₀ : Rd d) (c₁ : Rd d → ℝ) (c₂ c₃ c₄ : ℝ),
      (∀ γ ∈ Set.Ioc (0 : ℝ) η₀, IsProbabilityMeasure (πγ γ)) →
      Integrable f π → (∀ γ ∈ Set.Ioc (0 : ℝ) η₀, Integrable f (πγ γ)) →
      0 < α → 1 ≤ 𝔞 → 𝔞 ≤ 2 → 0 < η₀ → η₀ ≤ 1 / 2 →
      (∀ r, H1 P b σ (B r) f πγ α η₀ c₁) → (∀ r, H2 P b σ (B r) x₀ η₀ 𝔞 c₂) →
      H3 f π πγ η₀ 𝔞 δ c₃ → (∀ r, H4 P b σ (B r) x₀ η₀ c₁ c₄) →
      ∀ (γ₀ : ℝ) (R : ℕ) (τ T₀ : ℝ), 0 < γ₀ → γ₀ ≤ η₀ → α * γ₀ ≤ 1 → 1 ≤ R → 0 < T₀ →
      0 ≤ τ → τ ≤ geomHorizon T₀ 𝔞 R / 2 →
      eLpNorm (fun ω => estimator b σ x₀ γ₀ R τ (geomHorizon T₀ 𝔞) B f ω - ∫ y, f y ∂π) 2 P ^ 2
          ≤ ENNReal.ofReal (lipConst f ^ 2 *
              (cu / (α * T₀)
                  * (c₄ ^ 2 + max (c₂ ^ 2) (c₂ * c₄) * γ₀ ^ 𝔞 * Real.log γ₀⁻¹ * minTerm 𝔞 R)
                + (c₃ * levelStep γ₀ R ^ δ
                    + cu * c₁ x₀ / (α * T₀) * Real.exp (-α * τ)
                      * (2 : ℝ) ^ ((1 + 𝔞) / 2 * (R : ℝ))) ^ 2)) ∧
        cost R γ₀ (geomHorizon T₀ 𝔞)
          ≤ if 1 < 𝔞 then T₀ / γ₀ * (1 + 3 / 2 * ((2 : ℝ) ^ ((𝔞 - 1) / 2) - 1)⁻¹)
            else T₀ * (1 + 3 / 2 * (R : ℝ)) / γ₀ := by sorry

end MLLangevin.General
