-- Prove2me | Theorems.Thm_MLLangevin_ConvexA1_lemma_5_1_ii
-- name    : MLLangevin.ConvexA1.lemma_5_1_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:27:29.676997+00:00
-- url     : https://prove2.me/theorems/700df731-dbda-4adb-8f52-6e7573b12327
-- title:
--   Lemma 5.1 (ii), pp. 28–29 — 𝔼|X̄^{γ,x}_t − X̄^{γ,y}_t|² ≤ |x − y|²e^{−αt} and 𝒲₂(δ_x, π^γ) ≤ c₁(x)
-- statement:
--   Let $b$ be $L$-Lipschitz and satisfy $(\mathbf C_\alpha)$ with $0<\alpha\le L$, $\sigma>0$, $W$ a standard $d$-dimensional Brownian motion, $x^\star\in\mathbb R^d$ and $\gamma\in(0,\alpha/(2L^2)]$. Write $\bar X^{\gamma,x}$ for the continuous-time additive Euler scheme started at $x$ and driven by $W$.
--
--   1. For all $x,y\in\mathbb R^d$ and $t\ge0$, the two schemes driven by the same $W$ satisfy
--   $$\mathbb E\big[|\bar X^{\gamma,x}_t-\bar X^{\gamma,y}_t|^2\big]\le|x-y|^2e^{-\alpha t}.$$
--   2. For every invariant probability $\pi^\gamma$ of the scheme, every $x$ and every $n\ge0$, $\mathcal W_2(\mathcal L(\bar X^{\gamma,x}_{n\gamma}),\pi^\gamma)\le\mathcal W_2(\delta_x,\pi^\gamma)e^{-\alpha n\gamma}$, i.e. there is a coupling $\rho$ of $\mathcal L(\bar X^{\gamma,x}_{n\gamma})$ and $\pi^\gamma$ with $\big(\int|u-v|^2\rho(du,dv)\big)^{1/2}\le\big(\int|x-y|^2\pi^\gamma(dy)\big)^{1/2}e^{-\alpha n\gamma}$; and
--   $$\mathcal W_2(\delta_x,\pi^\gamma)=\Big(\int|x-y|^2\pi^\gamma(dy)\Big)^{1/2}\le c_1(x):=|x-x^\star|+\sqrt{|b(x^\star)|^2\Big(\frac1{L^2}+\frac2{\alpha^2}\Big)+\frac{2\sigma^2d}\alpha}.$$
--
--   The contraction gives exponential convergence to equilibrium of the scheme, uniformly in the step, which is the content of $(\mathbf H_1)$.
--
--   **Formalization Note** $\mathcal W_2$ to a Dirac mass is written as the explicit integral above, in $[0,\infty]$. The middle clause of the page, $\mathcal W_2(\mathcal L(\bar X^{\gamma,x}_{\underline t}),\pi^\gamma)\le\mathcal W_2(\delta_x,\pi^\gamma)e^{-\alpha\underline t}$, is stated at the grid times $\underline t=n\gamma$ as the existence of a coupling with that quadratic cost: Mathlib has no Wasserstein distance, and since an optimal coupling exists on $\mathbb R^d$ the two forms are equivalent.
-- source:
--   Egéa–Panloup, Multilevel-Langevin pathwise average for Gibbs approximation, arXiv:2109.07753v2, Lemma 5.1 (ii), pp. 28–29

import Mathlib
import Definitions.Def_MLLangevin_ConvexA1_Setting

namespace MLLangevin.ConvexA1

open MeasureTheory ProbabilityTheory EthierKurtz
open scoped ENNReal NNReal

/-- Lemma 5.1 (ii), pp. 28–29: L²-contraction of two continuous-time Euler schemes on the same
Brownian motion; `𝒲₂(ℒ(X̄^{γ,x}_{nγ}), π^γ) ≤ 𝒲₂(δ_x, π^γ) e^{−αnγ}`, written as the existence of a
coupling with that transport cost (optimal couplings exist, so this is the `𝒲₂` inequality); and
`𝒲₂(δ_x, π^γ) = (∫|x − y|² π^γ(dy))^{1/2} ≤ c₁(x)`, for every invariant probability `π^γ`. -/
theorem lemma_5_1_ii {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → SDEState d) (hW : IsStandardBrownian P W)
    (b : SDEState d → SDEState d) (L α σ : ℝ) (hLip : ∀ x y, ‖b x - b y‖ ≤ L * ‖x - y‖)
    (hC : CondC b α) (hα : 0 < α) (hαL : α ≤ L) (hσ : 0 < σ)
    (xs : SDEState d) (γ : ℝ) (hγ : 0 < γ) (hγL : γ ≤ α / (2 * L ^ 2)) :
    (∀ (x y : SDEState d) (t : ℝ≥0),
      eLpNorm (fun ω => eulerCont b σ γ x W t ω - eulerCont b σ γ y W t ω) 2 P ^ 2 ≤
        ENNReal.ofReal (‖x - y‖ ^ 2 * Real.exp (-α * (t : ℝ)))) ∧
    ∀ πγ : Measure (SDEState d), IsProbabilityMeasure πγ → IsInvChain P b σ γ W πγ →
      ∀ x : SDEState d,
        (∀ n : ℕ, ∃ ρ : Measure (SDEState d × SDEState d),
          ρ.map Prod.fst = P.map (eulerChain b σ γ x W n) ∧ ρ.map Prod.snd = πγ ∧
          (∫⁻ p, ENNReal.ofReal (‖p.1 - p.2‖ ^ 2) ∂ρ) ^ (1 / 2 : ℝ) ≤
            (∫⁻ y, ENNReal.ofReal (‖x - y‖ ^ 2) ∂πγ) ^ (1 / 2 : ℝ) *
              ENNReal.ofReal (Real.exp (-α * ((n : ℝ) * γ)))) ∧
        (∫⁻ y, ENNReal.ofReal (‖x - y‖ ^ 2) ∂πγ) ^ (1 / 2 : ℝ) ≤
          ENNReal.ofReal (c1fun b σ α L xs x) := by sorry

end MLLangevin.ConvexA1
