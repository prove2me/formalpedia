-- Prove2me | Theorems.Thm_MatroidProphetKW_RankOne_tail_bound
-- name    : MatroidProphetKW.RankOne.tail_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:24:40.490956+00:00
-- url     : https://prove2.me/theorems/75c1adb6-8e48-404a-a7cf-74db98623d1c
-- title:
--   §3.1, p. 5 — for x > T, Pr[X_τ > x] ≥ (1 − p) Σ_i Pr[X_i > x]
-- statement:
--   Let $X_1,\dots,X_n$ ($n\ge1$) be independent, non-negative random variables on a probability space with $\mathbb E[\max_i X_i] < \infty$. Let $T = \tfrac12\mathbb E[\max_i X_i]$, let $p = \Pr[\max_i X_i \ge T]$, and let $X_\tau$ be the reward of the rule that stops at the first $i$ with $X_i \ge T$ and collects $0$ if there is none. Then for every $x > T$,
--   $$\Pr[X_\tau > x] \;\ge\; (1-p)\sum_{i=1}^n \Pr[X_i > x].$$
--
--   This is the first step of the paper's rank-one analysis: it bounds the upper tail of the gambler's reward by the upper tails of the individual observations, discounted by the probability $1-p$ that the rule accepts nothing at all.
--
--   **Formalization Note** Independence is `iIndepFun X P` (mutual independence of the family); non-negativity is pointwise; $\Pr$ is `Measure.real`. $T$, $p$ and $X_\tau$ are the definitions of `MatroidProphetKW.RankOne.Setting`, not free parameters.
-- source:
--   Kleinberg & Weinberg, Matroid Prophet Inequalities, arXiv:1201.4764v1, p. 5, §3.1, display after "Then we get the following inequality, for any x > T:"

import Mathlib
import Definitions.Def_MatroidProphetKW_RankOne_Setting

namespace MatroidProphetKW.RankOne

open MeasureTheory ProbabilityTheory

/-- §3.1, p. 5: with `p = Pr[max_i X_i ≥ T]`, for every `x > T`,
`Pr[X_τ > x] ≥ (1 − p) ∑_{i=1}^n Pr[X_i > x]`. -/
theorem tail_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} [NeZero n] (X : Fin n → Ω → ℝ)
    (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hnonneg : ∀ i ω, 0 ≤ X i ω) (hint : Integrable (maxX X) P)
    (x : ℝ) (hx : thr P X < x) :
    (1 - stopProb P X) * ∑ i, P.real {ω | x < X i ω} ≤ P.real {ω | x < reward P X ω} := by sorry

end MatroidProphetKW.RankOne
