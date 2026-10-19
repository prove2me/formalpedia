-- Prove2me | Theorems.Thm_InfoRelaxTS_Monotone_lemma_1
-- name    : InfoRelaxTS.Monotone.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-13T23:31:14.894388+00:00
-- url     : https://prove2.me/theorems/5725b994-9c0b-4ab0-85ef-3ce3fb9c2aee
-- title:
--   Lemma 1, p. 56 — variant of Jensen's inequality: 𝔼[max{X + φ(X), 0}] ≥ 𝔼[max{𝔼X + φ(X), 0}]
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space, $\varphi : \mathbb R \to \mathbb R$ a non-decreasing function and $X$ a real random variable with $\mathbb E|X| < \infty$. Then
--
--   $$\mathbb E\big[\max\{X + \varphi(X), 0\}\big] \ge \mathbb E\big[\max\{\mathbb E(X) + \varphi(X), 0\}\big].$$
--
--   Replacing $X$ by its mean inside the first argument can only lower the expected positive part, even though $\varphi(X)$ keeps its randomness. This is the one-dimensional engine behind $W^{IRS.FH} \ge W^{IRS.V\text{-}Zero}$.
--
--   **Formalization Note** Both sides are expectations of nonnegative variables and are taken as lower Lebesgue integrals in $[0,\infty]$, so neither side can be a junk value. "Increasing" is read as non-decreasing (the paper's proof uses only monotonicity).
-- source:
--   Min, Maglaras, Moallemi, Thompson Sampling with Information Relaxation Penalties, arXiv:1902.04251v2, p. 56, Lemma 1, (125)

import Mathlib
import Definitions.Def_InfoRelaxTS_Monotone_Setting

namespace InfoRelaxTS.Monotone

open MeasureTheory ProbabilityTheory

/-- Lemma 1 (variant of Jensen's inequality), p. 56, (125): for a non-decreasing `φ : ℝ → ℝ` and an
integrable `X`, `𝔼[max{X + φ(X), 0}] ≥ 𝔼[max{𝔼(X) + φ(X), 0}]`. Both sides are expectations of
nonnegative variables, taken in `[0, ∞]`. -/
theorem lemma_1 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (φ : ℝ → ℝ) (hφ : Monotone φ) (X : Ω → ℝ) (hX : Integrable X μ) :
    ∫⁻ ω, ENNReal.ofReal (max ((∫ ω', X ω' ∂μ) + φ (X ω)) 0) ∂μ
      ≤ ∫⁻ ω, ENNReal.ofReal (max (X ω + φ (X ω)) 0) ∂μ := by sorry

end InfoRelaxTS.Monotone
