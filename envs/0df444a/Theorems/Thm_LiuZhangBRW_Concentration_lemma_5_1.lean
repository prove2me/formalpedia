-- Prove2me | Theorems.Thm_LiuZhangBRW_Concentration_lemma_5_1
-- name    : LiuZhangBRW.Concentration.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:18:36.977835+00:00
-- url     : https://prove2.me/theorems/3586ab74-ced1-4c68-b6ca-9cf43c55dd98
-- title:
--   Lemma 5.1 — $\mathbb E[e^{tX}]\le\exp(t^2/\delta^2\cdot\mathbb E[e^{\delta|X|}])$ for mean-zero $X$ and $|t|\le\delta$
-- statement:
--   Let $X$ be a real random variable with $\mathbb E(X)=0$. Then for all $\delta>0$ and all $t$ with $|t|/\delta\in[0,1]$,
--   $$
--   \mathbb E\bigl[e^{tX}\bigr]\le\exp\Bigl(\frac{t^2}{\delta^2}\,\mathbb E\bigl[e^{\delta|X|}\bigr]\Bigr).
--   $$
--   In particular, for $\delta=1$, $\mathbb E[e^{tX}]\le\exp(t^2\,\mathbb E[e^{|X|}])$ for $|t|\le1$, which is (5.1).
--
--   This replaces Hoeffding's lemma: it bounds the moment-generating function of a centred variable by its exponential absolute moment, without boundedness.
--
--   **Formalization Note** The exponential moment $\mathbb E[e^{\delta|X|}]$ is assumed finite (integrable); otherwise the right side is $+\infty$. Finiteness also makes $X$ and $e^{tX}$ integrable.
--
--   Differences from the source:
--   - encoding: E[e^{δ|X|}] on the right side (possibly +∞) → e^{δ|X|} integrable; reason: for an infinite exponential moment the claim is empty, and Lean's Bochner integral would return 0
--   - encoding: X a random variable with E(X) = 0 → X measurable on a probability space with ∫ X = 0; reason: random variables are measurable; integrability of X follows from that of e^{δ|X|}
-- source:
--   Liu, Zhang, Concentration Inequalities for Branching Random Walks with Applications to Phase Transitions in CSPs, arXiv:1601.04794 (artifact sha256 7499631b9d550f66e791c0b3df0879f26102f111fee3052e363ebbff0c72bdcb; no version stamp), Lemma 5.1 and (5.1), p. 7

import Mathlib

open MeasureTheory

namespace LiuZhangBRW.Concentration

/-- Lemma 5.1 (Liu, Zhang, *Concentration Inequalities for Branching Random Walks with Applications to
Phase Transitions in CSPs*, arXiv:1601.04794, artifact sha256 7499631b…bdcb, p. 7). If `E(X) = 0`,
then for all `δ > 0` and `|t|/δ ∈ [0, 1]`, `E[e^{tX}] ≤ exp(t²/δ² · E[e^{δ|X|}])`.
The case `δ = 1` is (5.1).

**Formalization Note** `X` is a measurable real random variable on a probability space. The
integrability of `e^{δ|X|}` is assumed: without it the paper's right side is `+∞` and the
claim is empty, while Lean's Bochner integral would return `0`. It implies that `X` and `e^{tX}`
are integrable. -/
theorem lemma_5_1 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Measurable X) (hmean : ∫ ω, X ω ∂μ = 0) (δ t : ℝ) (hδ : 0 < δ)
    (ht : |t| / δ ≤ 1) (hexp : Integrable (fun ω => Real.exp (δ * |X ω|)) μ) :
    ∫ ω, Real.exp (t * X ω) ∂μ ≤ Real.exp (t ^ 2 / δ ^ 2 * ∫ ω, Real.exp (δ * |X ω|) ∂μ) := by sorry

end LiuZhangBRW.Concentration
