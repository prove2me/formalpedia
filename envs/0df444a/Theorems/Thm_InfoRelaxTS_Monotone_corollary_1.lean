-- Prove2me | Theorems.Thm_InfoRelaxTS_Monotone_corollary_1
-- name    : InfoRelaxTS.Monotone.corollary_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-13T23:31:29.016511+00:00
-- url     : https://prove2.me/theorems/93794d04-6395-4ffd-acd4-ef48f88c0aa8
-- title:
--   Corollary 1, p. 57 — conditional variant: 𝔼[max{X + φ(X,·), 0}] ≥ 𝔼[max{𝔼(X|ℋ) + φ(X,·), 0}]
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space, $\mathcal H \subseteq \mathcal F$ a sub-$\sigma$-field, $X$ an integrable random variable, and $\varphi : \mathbb R \times \Omega \to \mathbb R$ such that
--
--   1. $x \mapsto \varphi(x,\omega)$ is non-decreasing for each $\omega$;
--   2. $\omega \mapsto \varphi(x,\omega)$ is $\mathcal H$-measurable for each $x$ ($\varphi(\cdot,\omega)$ is a deterministic function given $\mathcal H$).
--
--   Then
--
--   $$\mathbb E\big[\max\{X(\omega) + \varphi(X(\omega),\omega), 0\}\big] \ge \mathbb E\big[\max\{\mathbb E(X\mid\mathcal H)(\omega) + \varphi(X(\omega),\omega), 0\}\big].$$
--
--   This is Lemma 1 conditioned on $\mathcal H$; Corollary 2 applies it to a maximum of affine functions of $X$.
--
--   **Formalization Note** Added, disclosed: $\varphi$ is jointly measurable for $\mathcal B(\mathbb R) \otimes \mathcal H$, so that $\omega \mapsto \varphi(X(\omega),\omega)$ is a random variable, which the page's expectations presuppose and (i)–(ii) do not imply. $\mathbb E|X| < \infty$ is inherited from Lemma 1. Both sides are lower Lebesgue integrals in $[0,\infty]$. "Increasing" means non-decreasing.
-- source:
--   Min, Maglaras, Moallemi, Thompson Sampling with Information Relaxation Penalties, arXiv:1902.04251v2, p. 57, Corollary 1, (133)

import Mathlib
import Definitions.Def_InfoRelaxTS_Monotone_Setting

namespace InfoRelaxTS.Monotone

open MeasureTheory ProbabilityTheory

/-- Corollary 1, p. 57, (133): the conditional version of Lemma 1. `φ(x, ω)` is non-decreasing in
`x` for each `ω`, `ℋ`-measurable in `ω` for each `x`, and (disclosed) jointly measurable for
`Borel(ℝ) ⊗ ℋ`; `X` is integrable. Then
`𝔼[max{X + φ(X, ·), 0}] ≥ 𝔼[max{𝔼(X|ℋ) + φ(X, ·), 0}]`, both sides in `[0, ∞]`. -/
theorem corollary_1 {Ω : Type*} {mH mΩ : MeasurableSpace Ω} (hmH : mH ≤ mΩ)
    (μ : @Measure Ω mΩ) [@IsProbabilityMeasure Ω mΩ μ]
    (φ : ℝ → Ω → ℝ) (hmono : ∀ ω, Monotone fun x => φ x ω)
    (hmeas : ∀ x, Measurable[mH] (φ x))
    (hjoint : @Measurable (ℝ × Ω) ℝ (@Prod.instMeasurableSpace ℝ Ω _ mH) _ (Function.uncurry φ))
    (X : Ω → ℝ) (hX : Integrable X μ) :
    ∫⁻ ω, ENNReal.ofReal (max ((μ[X | mH]) ω + φ (X ω) ω) 0) ∂μ
      ≤ ∫⁻ ω, ENNReal.ofReal (max (X ω + φ (X ω) ω) 0) ∂μ := by sorry

end InfoRelaxTS.Monotone
