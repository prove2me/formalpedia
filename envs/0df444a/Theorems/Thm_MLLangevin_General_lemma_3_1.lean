-- Prove2me | Theorems.Thm_MLLangevin_General_lemma_3_1
-- name    : MLLangevin.General.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:10:11.462976+00:00
-- url     : https://prove2.me/theorems/cb724749-7bca-431f-bf47-269f9388c3ea
-- title:
--   Lemma 3.1, p. 21 — |(T − τ)⁻¹∫_τ^T 𝔼_x[f(X̄^γ_{s̲_η})] − π^γ(f) ds| ≤ 2e^{αη}c₁(x)[f]₁e^{−ατ}/(αT) for η ∈ {γ, 2γ}
-- statement:
--   Assume $(\mathbf H_1)$ for a driving Brownian motion $W$, a Lipschitz function $f$, a rate $\alpha>0$, a step bound $\eta_0$, measures $\pi^\gamma$ and a function $c_1$. Let $\gamma\in(0,\eta_0]$ and let $\eta=\gamma$ or $\eta=2\gamma$. Let $\tau$ and $T$ be positive numbers with $\tau\le T/2$. Then, for every $x\in\mathbb R^d$,
--   $$\left|\frac1{T-\tau}\int_\tau^T\Big(\mathbb E_x\big[f(\bar X^{\gamma,x}_{\underline{s}_\eta})\big]-\pi^\gamma(f)\Big)ds\right|\le\frac{2e^{\alpha\eta}c_1(x)[f]_1e^{-\alpha\tau}}{\alpha T},$$
--   where $\underline{s}_\eta=\eta\lfloor s/\eta\rfloor$ is a grid time of the scheme of step $\gamma$.
--
--   The lemma controls the long-time part of the bias of each level of the multilevel occupation measure: it is applied with $(\gamma,\eta)=(\gamma_0,\gamma_0)$, $(\gamma_r,\gamma_{r-1})$ and $(\gamma_{r-1},\gamma_{r-1})$.
--
--   **Formalization Note.** $\eta=m\gamma$ with $m\in\{1,2\}$, and $\bar X^\gamma$ at time $\underline{s}_\eta$ is step $m\lfloor s/(m\gamma)\rfloor$ of the chain. The page writes the scheme as $\bar X^{\gamma,x_0}$ inside $\mathbb E_x$; the expectation under $\mathbb E_x$ is that of the scheme started at $x$, which is how the proof applies $(\mathbf H_1)$, so the Lean chain starts at $x$. The standing assumptions of the paper (Lipschitz $b,\sigma,f$; $W$ a standard Brownian motion) are kept as hypotheses.
-- source:
--   Egéa–Panloup, arXiv:2109.07753v2, Lemma 3.1, p. 21 (proof p. 22)

import Mathlib
import Definitions.Def_MLLangevin_General_Setting

namespace MLLangevin.General

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

theorem lemma_3_1 {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → Rd d) (hW : EthierKurtz.IsStandardBrownian P W)
    (b : Rd d → Rd d) (σ : Rd d → (Rd d →L[ℝ] Rd d))
    (hb : ∃ K, LipschitzWith K b) (hσ : ∃ K, LipschitzWith K σ)
    (f : Rd d → ℝ) (hf : ∃ K, LipschitzWith K f) (πγ : ℝ → Measure (Rd d))
    (α η₀ : ℝ) (c₁ : Rd d → ℝ) (hα : 0 < α) (hH1 : H1 P b σ W f πγ α η₀ c₁)
    (γ : ℝ) (hγ : γ ∈ Set.Ioc (0 : ℝ) η₀) (m : ℕ) (hm : m = 1 ∨ m = 2)
    (τ T : ℝ) (hτ : 0 < τ) (hT : 0 < T) (hτT : τ ≤ T / 2) (x : Rd d) :
    |(T - τ)⁻¹ * ∫ s in τ..T,
        (∫ ω, f (eulerChain b σ γ x W (m * ⌊s / ((m : ℝ) * γ)⌋₊) ω) ∂P - ∫ y, f y ∂(πγ γ))|
      ≤ 2 * Real.exp (α * ((m : ℝ) * γ)) * c₁ x * lipConst f * Real.exp (-α * τ) / (α * T) := by sorry

end MLLangevin.General
