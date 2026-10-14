-- Prove2me | Theorems.Thm_MLLangevin_ConvexA2_lemma_5_1_iii
-- name    : MLLangevin.ConvexA2.lemma_5_1_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:32:58.734877+00:00
-- url     : https://prove2.me/theorems/dd917463-feb3-4116-b473-1a1b7f356ac3
-- title:
--   Lemma 5.1 (iii), p. 29 — with η₀ = α/(2L²), (H₁) holds with c₁ (at rate α/2) and (H₄) holds with c₄² ≲_uc α⁻²|b(x₀)|² + σ²α⁻¹d
-- statement:
--   Assume $(\mathbf C_\alpha)$, that $b$ is $L$-Lipschitz with $0<\alpha\le L$, and $\sigma>0$. Let $B^{(0)},B^{(1)},\dots$ be standard $d$-dimensional Brownian motions, $x_0\in\mathbb R^d$, $\eta_0=\alpha/(2L^2)$, and
--   $$c_1(x)=|x-x_0|+\sqrt{|b(x_0)|^2\Big(\frac1{L^2}+\frac2{\alpha^2}\Big)+\frac{2\sigma^2d}{\alpha}} .$$
--   There is a universal constant $\mathfrak c_u$, independent of $d$, $b$, $\sigma$, $\alpha$, $L$, $x_0$ and the probability space, such that:
--
--   1. for every Lipschitz $f:\mathbb R^d\to\mathbb R$, assumption $(\mathbf H_1)$ holds with this $c_1$, $\eta_0$ and the exponential rate $\alpha/2$: for every level $r$, start $x$, $\gamma\in(0,\eta_0]$, invariant probability $\pi^\gamma$ with $f\in L^1(\pi^\gamma)$ and $n\ge0$,
--   $$\big|\mathbb E[f(\bar X^{\gamma,x}_{n\gamma})]-\pi^\gamma(f)\big|\le c_1(x)[f]_1e^{-\frac\alpha2n\gamma};$$
--   2. assumption $(\mathbf H_4)$ holds with this $c_1$, $\eta_0$ and a constant $c_4\ge0$ satisfying
--   $$c_4^2\le\mathfrak c_u\big(\alpha^{-2}|b(x_0)|^2+\sigma^2\alpha^{-1}d\big).$$
--
--   This turns the stability estimates of Lemma 5.1 (i)–(ii) into the hypotheses $(\mathbf H_1)$ and $(\mathbf H_4)$ of the general complexity theorem.
--
--   **Formalization Note** The paper states $(\mathbf H_1)$ with the rate $\alpha$, from the bound $\mathcal W_2(\bar X^{\gamma,x}_{\underline t},\pi^\gamma)\le\mathcal W_2(\delta_x,\pi^\gamma)e^{-\alpha\underline t}$ of Lemma 5.1(ii). Its proof gives $\mathbb E|\bar X^{\gamma,x}_t-\bar X^{\gamma,y}_t|^2\le|x-y|^2e^{-\alpha t}$, a contraction of the squared distance, hence the rate $\alpha/2$ for $\mathcal W_2$ and for $(\mathbf H_1)$. The rate $\alpha$ is false in general: for the drift $b(x)=-\alpha x+\omega Jx$ on $\mathbb R^2$ ($J$ a rotation by $\pi/2$, $L^2=\alpha^2+\omega^2$), one step contracts distances by exactly $\sqrt{1-\frac32\alpha\gamma}$ at $\gamma=\alpha/(2L^2)$. The item states the rate the proof gives. The constant $\mathfrak c_u$ is quantified before every datum.
-- source:
--   Egéa–Panloup, arXiv:2109.07753v2, Lemma 5.1 (ii)–(iii), pp. 28–29

import Mathlib
import Definitions.Def_MLLangevin_ConvexA2_Multilevel
import Definitions.Def_MLLangevin_ConvexA2_DriftNorms

open MeasureTheory ProbabilityTheory EthierKurtz
open scoped ENNReal NNReal

namespace MLLangevin.ConvexA2

theorem lemma_5_1_iii :
    ∃ cu : ℝ, ∀ {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (B : ℕ → ℝ≥0 → Ω → SDEState d), (∀ r, IsStandardBrownian P (B r)) →
      ∀ (b : SDEState d → SDEState d) (L α σ : ℝ),
      (∀ x y, ‖b x - b y‖ ≤ L * ‖x - y‖) → MLLangevin.ConvexA1.CondC b α → 0 < α → α ≤ L → 0 < σ →
      ∀ x₀ : SDEState d,
        (∀ f : SDEState d → ℝ, (∃ K, LipschitzWith K f) →
          H1 P b σ B f (α / 2) (α / (2 * L ^ 2)) (MLLangevin.ConvexA1.c1fun b σ α L x₀)) ∧
        ∃ c₄ : ℝ, H4 P b σ B x₀ (α / (2 * L ^ 2)) (MLLangevin.ConvexA1.c1fun b σ α L x₀) c₄ ∧
          c₄ ^ 2 ≤ cu * ((α ^ 2)⁻¹ * ‖b x₀‖ ^ 2 + σ ^ 2 * α⁻¹ * d) := by sorry

end MLLangevin.ConvexA2
