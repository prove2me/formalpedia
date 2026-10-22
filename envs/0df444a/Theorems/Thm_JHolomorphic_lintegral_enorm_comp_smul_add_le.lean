-- Prove2me | Theorems.Thm_JHolomorphic_lintegral_enorm_comp_smul_add_le
-- name    : JHolomorphic.lintegral_enorm_comp_smul_add_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-21T21:03:58.060069+00:00
-- url     : https://prove2.me/theorems/943e1b6b-34b6-4565-b2e8-ef38b0632f45
-- title:
--   Hölder bound for integrals of rescaled translates over a set of finite measure in $\mathbb{C}$
-- statement:
--   Let $\mu$ be an additive Haar measure on $\mathbb{C}$, let $E$ be a normed space, $1\le p<\infty$, and let $F:\mathbb{C}\to E$ be $\mu$-a.e. strongly measurable. For every $s>0$, $a\in\mathbb{C}$ and every set $S\subseteq\mathbb{C}$,
--   $$\int_S \|F(s w+a)\|\,d\mu(w)\;\le\; s^{-2/p}\,\|F\|_{L^p(\mu)}\,\mu(S)^{1-1/p}.$$
--   Both sides are in $[0,\infty]$. The factor $s^{-2/p}$ reflects the real dimension $2$ of $\mathbb{C}$. The estimate is a reusable tool for pointwise bounds of Sobolev maps in the plane.
--
--   **Formalization Note** The left side is the lower Lebesgue integral `∫⁻ w in S, ‖F (s • w + a)‖ₑ ∂μ`, with real scalar multiplication `s • w`. The $L^p$ norm is `eLpNorm F (ENNReal.ofReal p) μ` and $\mu(S)^{1-1/p}$ is the `ℝ≥0∞` power `μ S ^ (1 - 1 / p)`. $S$ is arbitrary (not assumed measurable) and $\mu$ is any measure with `[μ.IsAddHaarMeasure]`.
-- source:
--   Standard (Hölder's inequality and scaling of Haar measure).

import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

namespace JHolomorphic

open MeasureTheory Metric

/-- Let `μ` be an additive Haar measure on `ℂ`, `1 ≤ p`, `F : ℂ → E` a.e. strongly measurable,
`s > 0`, `a ∈ ℂ` and `S ⊆ ℂ`. Then `∫_S ‖F(s w + a)‖ dμ(w) ≤ s^{-2/p} ‖F‖_{L^p(μ)} μ(S)^{1-1/p}`. -/
theorem lintegral_enorm_comp_smul_add_le {E : Type*} [NormedAddCommGroup E]
    (μ : Measure ℂ) [μ.IsAddHaarMeasure] {p : ℝ} (hp : 1 ≤ p) {F : ℂ → E}
    (hF : AEStronglyMeasurable F μ) {s : ℝ} (hs : 0 < s) (a : ℂ) (S : Set ℂ) :
    ∫⁻ w in S, ‖F (s • w + a)‖ₑ ∂μ ≤
      ENNReal.ofReal (s ^ (-2 / p)) * eLpNorm F (ENNReal.ofReal p) μ * μ S ^ (1 - 1 / p) := by
  sorry

end JHolomorphic
