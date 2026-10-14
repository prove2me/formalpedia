-- Prove2me | Theorems.Thm_MLLangevin_ConvexA1_lemma_5_1_iii
-- name    : MLLangevin.ConvexA1.lemma_5_1_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:27:19.931776+00:00
-- url     : https://prove2.me/theorems/af82dd66-f1f4-4146-b80f-1ec23500b425
-- title:
--   Lemma 5.1 (iii), p. 29 — with η₀ = α/(2L²), (H₁) holds with c₁ and (H₄) with c₄² ≲_uc α⁻²|b(x₀)|² + σ²α⁻¹d
-- statement:
--   There is a universal constant $\mathfrak c_u$ with the following property. Let $b$ be $L$-Lipschitz and satisfy $(\mathbf C_\alpha)$ with $0<\alpha\le L$, $\sigma>0$, $W$ a standard $d$-dimensional Brownian motion and $x_0\in\mathbb R^d$. Set $\eta_0=\alpha/(2L^2)$ and let $c_1(x)=|x-x_0|+\sqrt{|b(x_0)|^2(\frac1{L^2}+\frac2{\alpha^2})+\frac{2\sigma^2d}\alpha}$ (the function of Lemma 5.1 (ii) with $x^\star=x_0$). Then:
--
--   1. for every Lipschitz $f:\mathbb R^d\to\mathbb R$, assumption $(\mathbf H_1)$ holds with this $c_1$, rate $\alpha$ and $\eta_0$;
--   2. there is $c_4\ge0$ such that $(\mathbf H_4)$ holds with this $c_1$ and $\eta_0$, and
--   $$c_4^2\le\mathfrak c_u\big(\alpha^{-2}|b(x_0)|^2+\sigma^2\alpha^{-1}d\big).$$
--
--   This is the step that turns the moment and contraction bounds of Lemma 5.1 (i)–(ii) into the abstract assumptions under which the multilevel complexity theorem applies.
--
--   **Formalization Note** "$\lesssim_{uc}$" is an existential constant quantified before every datum (dimension, probability space, $b$, $\sigma$, $\alpha$, $L$, $x_0$). $(\mathbf H_4)$ is over all $t\ge0$ of the continuous-time scheme, as on the page.
-- source:
--   Egéa–Panloup, Multilevel-Langevin pathwise average for Gibbs approximation, arXiv:2109.07753v2, Lemma 5.1 (iii), p. 29

import Mathlib
import Definitions.Def_MLLangevin_ConvexA1_Setting

namespace MLLangevin.ConvexA1

open MeasureTheory ProbabilityTheory EthierKurtz
open scoped ENNReal NNReal

/-- Lemma 5.1 (iii), p. 29: with `η₀ = α/(2L²)`, (H₁) holds with `c₁` of Lemma 5.1 (ii)
(`x⋆ = x₀`) for every Lipschitz `f`, and (H₄) holds with `c₄² ≲_uc α⁻²|b(x₀)|² + σ²α⁻¹d`. -/
theorem lemma_5_1_iii : ∃ cu : ℝ, ∀ {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → SDEState d) (_hW : IsStandardBrownian P W)
    (b : SDEState d → SDEState d) (L α σ : ℝ) (_hLip : ∀ x y, ‖b x - b y‖ ≤ L * ‖x - y‖)
    (_hC : CondC b α) (_hα : 0 < α) (_hαL : α ≤ L) (_hσ : 0 < σ) (x₀ : SDEState d),
    (∀ f : SDEState d → ℝ, (∃ K, LipschitzWith K f) →
      H1 P b σ W f α (α / (2 * L ^ 2)) (c1fun b σ α L x₀)) ∧
    ∃ c₄ : ℝ, H4 P b σ W x₀ (α / (2 * L ^ 2)) (c1fun b σ α L x₀) c₄ ∧
      c₄ ^ 2 ≤ cu * (α⁻¹ ^ 2 * ‖b x₀‖ ^ 2 + σ ^ 2 * α⁻¹ * (d : ℝ)) := by sorry

end MLLangevin.ConvexA1
