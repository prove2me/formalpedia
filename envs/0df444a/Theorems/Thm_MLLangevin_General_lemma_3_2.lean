-- Prove2me | Theorems.Thm_MLLangevin_General_lemma_3_2
-- name    : MLLangevin.General.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:10:12.858169+00:00
-- url     : https://prove2.me/theorems/02850cd6-9751-4380-aeed-28605efd2841
-- title:
--   Lemma 3.2, p. 23 — Var((T − τ)⁻¹∫_τ^T G^γ_s ds) ≤ 𝔠_var[f]₁²γ^𝔞log(1/γ)/(T − τ), 𝔠_var = 16eα⁻¹max(c₂², c₂c₄)
-- statement:
--   Let $W$ be a standard $d$-dimensional Brownian motion, $b,\sigma$ Lipschitz and $f$ Lipschitz. Let $0\le\tau<T$. Assume $(\mathbf H_1)$, $(\mathbf H_2)$ and $(\mathbf H_4)$ for $W$, for some $\mathfrak a\in[1,2]$, $\gamma_0\in[0,\eta_0]$ and $x_0\in\mathbb R^d$, with $0<\alpha\le1$. Let $\gamma\in(0,\gamma_0]$ with $\alpha\gamma\le1$ and $\gamma\le1/2$. Then
--   $$\operatorname{Var}\Big(\frac1{T-\tau}\int_\tau^TG^\gamma_s\,ds\Big)\le\frac{\mathfrak c_{var}[f]_1^2}{T-\tau}\gamma^{\mathfrak a}\log\Big(\frac1\gamma\Big),\qquad \mathfrak c_{var}=16e\,\alpha^{-1}\max(c_2^2,c_2c_4),$$
--   where $G^\gamma_s=f(\bar X^{\gamma/2,x_0}_{\underline{s}_\gamma})-f(\bar X^{\gamma,x_0}_{\underline{s}_\gamma})$, both schemes driven by $W$.
--
--   This is the variance bound of one correcting level: $L^2$-confluence $(\mathbf H_2)$ controls short-range covariances and the exponential ergodicity $(\mathbf H_1)$ long-range ones.
--
--   **Formalization Note.** Two hypotheses are added to the page: $\gamma\le1/2$ and $\alpha\le1$, the standing ranges $\eta_0\le1/2$, $\alpha\le1$ of Theorem 2.1 under which the lemma is used. As printed (with only $\gamma\le\gamma_0\le\eta_0$ and $\alpha\gamma\le1$) the bound fails at $\gamma\ge1$, where its right side is $\le0$. Var is `evariance`, valued in $[0,\infty]$.
-- source:
--   Egéa–Panloup, arXiv:2109.07753v2, Lemma 3.2, p. 23 (proof pp. 23–24)

import Mathlib
import Definitions.Def_MLLangevin_General_Setting

namespace MLLangevin.General

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

theorem lemma_3_2 {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → Rd d) (hW : EthierKurtz.IsStandardBrownian P W)
    (b : Rd d → Rd d) (σ : Rd d → (Rd d →L[ℝ] Rd d))
    (hb : ∃ K, LipschitzWith K b) (hσ : ∃ K, LipschitzWith K σ)
    (f : Rd d → ℝ) (hf : ∃ K, LipschitzWith K f) (πγ : ℝ → Measure (Rd d))
    (α 𝔞 η₀ : ℝ) (x₀ : Rd d) (c₁ : Rd d → ℝ) (c₂ c₄ : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (h𝔞 : 1 ≤ 𝔞 ∧ 𝔞 ≤ 2)
    (hH1 : H1 P b σ W f πγ α η₀ c₁) (hH2 : H2 P b σ W x₀ η₀ 𝔞 c₂)
    (hH4 : H4 P b σ W x₀ η₀ c₁ c₄)
    (τ T : ℝ) (hτ : 0 ≤ τ) (hτT : τ < T) (γ₀ : ℝ) (hγ₀ : 0 ≤ γ₀ ∧ γ₀ ≤ η₀)
    (γ : ℝ) (hγ : 0 < γ ∧ γ ≤ γ₀) (hαγ : α * γ ≤ 1) (hγ2 : γ ≤ 1 / 2) :
    evariance (fun ω => (T - τ)⁻¹ * ∫ s in τ..T, Gproc b σ f γ x₀ W s ω) P
      ≤ ENNReal.ofReal (16 * Real.exp 1 * α⁻¹ * max (c₂ ^ 2) (c₂ * c₄) * lipConst f ^ 2
          / (T - τ) * γ ^ 𝔞 * Real.log (1 / γ)) := by sorry

end MLLangevin.General
