-- Prove2me | Theorems.Thm_HindsightGain_Uniform_lemma_3_2
-- name    : HindsightGain.Uniform.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:52:58.665929+00:00
-- url     : https://prove2.me/theorems/aa527ea6-164c-4696-a3db-e06fdf63cba1
-- title:
--   Lemma 3.2 — Fluctuation bound
-- statement:
--   Fix a model with $n,D\ge1$, $r\ge2$, and independent nonnegative random weights $\zeta_i$ on a probability space with finite second moments. With $p_i=\mathbb E\zeta_i$, the support-function maximum $\Delta$ and variance scale $V$ are exactly (20):
--   $$\Delta=\max_{\|w\|\le1}\sum_i(\zeta_i-p_i)h_{K_i}(L_iw),\qquad V^2=\sum_i\operatorname{Var}(\zeta_i)\|L_i\|_F^2.$$
--   Then $\Delta$ is square integrable and all three bounds hold:
--   $$\mathbb E\Delta\le2V,\qquad \operatorname{Var}\Delta\le V^2,\qquad \mathbb E\Delta^2\le5V^2.$$
--   This controls the mean, variance and second moment of the actual fluctuation without assuming bounded weights or any higher moment.
--
--   Differences from the source:
--   - encoding: arbitrary multilinear interactions on r-element subsets of [n] and Euclidean local domains → coefficient arrays on cardinality-r Finsets of Fin n, with each interaction evaluated in increasing order in EuclideanSpace ℝ (Fin D); reason: orthonormal coordinates encode every source multilinear map uniquely, preserving its coefficient Frobenius norm and every compact local domain
--   - encoding: nonnegative random variables with finite second moments → almost-everywhere nonnegativity and MemLp at exponent 2 for each weight; reason: random variables are identified up to null sets, and MemLp includes the measurable representative and finite second moment
--   - encoding: support-function maxima and the maximum over the tensor unit ball in (20) → real sSup of their concrete objective images; reason: Model supplies nonempty compact local sets and the finite-dimensional tensor unit ball is nonempty compact, so all these suprema are finite attained maxima
--   - encoding: the maximum Δ is square integrable, as stated immediately before the lemma → MemLp Δ 2 is included in the conclusion alongside all three inequalities; reason: this makes the source expectations genuine integrals and does not add a hypothesis
-- source:
--   Xiaohui Bei, Wenhao Wu, The Optimizer's Windfall: Bounding Hindsight Gain under Random Restrictions, STOC 2027 submission #464 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/464.pdf, Lemma 3.2 and (20), p.16; proof p.17

import Mathlib
import Definitions.Def_HindsightGain_Uniform_fluctuations

set_option autoImplicit false
open MeasureTheory ProbabilityTheory

namespace HindsightGain.Uniform

/-- Lemma 3.2, p.16, all three bounds for exactly (20).
Square integrability of Delta is asserted, rather than imposed on the weights. -/
theorem lemma_3_2 {Ω : Type} [MeasurableSpace Ω] {n D r : ℕ}
    (M : Model n D r) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ζ : Fin n → Ω → ℝ) (hindep : iIndepFun ζ μ)
    (hnonneg : ∀ i, ∀ᵐ ω ∂μ, 0 ≤ ζ i ω) (hsecond : ∀ i, MemLp (ζ i) 2 μ) :
    MemLp (fluctuationRV M μ ζ) 2 μ ∧
      (∫ ω, fluctuationRV M μ ζ ω ∂μ) ≤ 2 * varianceScale M μ ζ ∧
      variance (fluctuationRV M μ ζ) μ ≤ varianceScale M μ ζ ^ 2 ∧
      (∫ ω, fluctuationRV M μ ζ ω ^ 2 ∂μ) ≤ 5 * varianceScale M μ ζ ^ 2 := by sorry

end HindsightGain.Uniform
