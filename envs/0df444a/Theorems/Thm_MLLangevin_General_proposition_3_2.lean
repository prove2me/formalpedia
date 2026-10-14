-- Prove2me | Theorems.Thm_MLLangevin_General_proposition_3_2
-- name    : MLLangevin.General.proposition_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:10:38.114292+00:00
-- url     : https://prove2.me/theorems/a0020f9b-1eb7-4e7a-9352-d5860d569b5b
-- title:
--   Proposition 3.2, p. 22 — bias (30): |𝔼[𝒴] − π(f)| ≤ c₃[f]₁γ_R^δ + 8e^{2αγ₀}c₁(x₀)[f]₁e^{−ατ}2^{((1+𝔞)/2)R}/(αT₀)
-- statement:
--   Let $B^{(0)},B^{(1)},\dots$ be independent standard $d$-dimensional Brownian motions and let $b,\sigma,f$ be Lipschitz. Let $\pi$ be a probability measure and $(\pi^\gamma)_{\gamma\in(0,\eta_0]}$ probability measures, $f$ integrable for each of them. Assume $(\mathbf H_1)$ (for every level's Brownian motion), $(\mathbf H_3)$ and $(\mathbf H_4)$ (for every level's Brownian motion) for some $\mathfrak a\in[1,2]$, $\eta_0\in(0,1]$, $\alpha>0$ and $x_0\in\mathbb R^d$. Let $\gamma_0\in(0,\eta_0]$ and $R\ge1$, let $\tau>0$ and $T_0>0$ satisfy $2\tau\le T_R$, where $T_r=T_02^{-\frac{1+\mathfrak a}2r}$ and $\gamma_r=\gamma_02^{-r}$. Then the multilevel occupation measure $\mathcal Y=\mathcal Y(R,(\gamma_r)_r,\tau,(T_r)_r,x_0,f)$ is integrable and
--   $$\big|\mathbb E_{x_0}[\mathcal Y]-\pi(f)\big|\le c_3[f]_1\gamma_R^\delta+\frac{8e^{2\alpha\gamma_0}c_1(x_0)[f]_1}{\alpha T_0}e^{-\alpha\tau}2^{\frac{1+\mathfrak a}2R}.$$
--
--   The first term is the discretization bias of the finest level, the second the long-time bias of all levels, which the warm start $\tau$ makes small.
--
--   **Formalization Note.** The integrability of $\mathcal Y$ is part of the conclusion, so the expectation is not a default value. The page states $\eta_0\in[0,1]$; $\eta_0>0$ is the standing assumption ("a positive $\eta_0$", p. 6). $(\mathbf H_4)$ is a hypothesis of the page and is kept although the bound does not involve $c_4$.
-- source:
--   Egéa–Panloup, arXiv:2109.07753v2, Proposition 3.2 and (30), p. 22 (proof (31), p. 23)

import Mathlib
import Definitions.Def_MLLangevin_General_Setting

namespace MLLangevin.General

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

theorem proposition_3_2 {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (B : ℕ → ℝ≥0 → Ω → Rd d)
    (hB : ∀ r, EthierKurtz.IsStandardBrownian P (B r))
    (hind : iIndepFun (fun r ω => fun t => B r t ω) P)
    (b : Rd d → Rd d) (σ : Rd d → (Rd d →L[ℝ] Rd d))
    (hb : ∃ K, LipschitzWith K b) (hσ : ∃ K, LipschitzWith K σ)
    (f : Rd d → ℝ) (hf : ∃ K, LipschitzWith K f)
    (π : Measure (Rd d)) [IsProbabilityMeasure π] (πγ : ℝ → Measure (Rd d))
    (α 𝔞 δ η₀ : ℝ) (x₀ : Rd d) (c₁ : Rd d → ℝ) (c₃ c₄ : ℝ)
    (hπγ : ∀ γ ∈ Set.Ioc (0 : ℝ) η₀, IsProbabilityMeasure (πγ γ))
    (hfπ : Integrable f π) (hfπγ : ∀ γ ∈ Set.Ioc (0 : ℝ) η₀, Integrable f (πγ γ))
    (hα : 0 < α) (h𝔞 : 1 ≤ 𝔞 ∧ 𝔞 ≤ 2) (hη₀ : 0 < η₀ ∧ η₀ ≤ 1)
    (hH1 : ∀ r, H1 P b σ (B r) f πγ α η₀ c₁) (hH3 : H3 f π πγ η₀ 𝔞 δ c₃)
    (hH4 : ∀ r, H4 P b σ (B r) x₀ η₀ c₁ c₄)
    (γ₀ : ℝ) (hγ₀ : 0 < γ₀ ∧ γ₀ ≤ η₀) (R : ℕ) (hR : 1 ≤ R) (τ T₀ : ℝ) (hτ : 0 < τ)
    (hT₀ : 0 < T₀) (hτR : 2 * τ ≤ geomHorizon T₀ 𝔞 R) :
    Integrable (estimator b σ x₀ γ₀ R τ (geomHorizon T₀ 𝔞) B f) P ∧
      |∫ ω, estimator b σ x₀ γ₀ R τ (geomHorizon T₀ 𝔞) B f ω ∂P - ∫ y, f y ∂π|
        ≤ c₃ * lipConst f * levelStep γ₀ R ^ δ
          + 8 * Real.exp (2 * α * γ₀) * c₁ x₀ * lipConst f / (α * T₀) * Real.exp (-α * τ)
            * (2 : ℝ) ^ ((1 + 𝔞) / 2 * (R : ℝ)) := by sorry

end MLLangevin.General
