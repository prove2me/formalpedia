-- Prove2me | Theorems.Thm_MatroidProphetKW_RankOne_tail_bound_max
-- name    : MatroidProphetKW.RankOne.tail_bound_max
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:25:38.267976+00:00
-- url     : https://prove2.me/theorems/54299dcd-ab5b-46e0-b197-c9708d6ae5b4
-- title:
--   §3.1, p. 5 — for all x > T, Pr[X_τ > x] ≥ (1 − p) Pr[max_i X_i > x]
-- statement:
--   Let $X_1,\dots,X_n$ ($n\ge1$) be independent, non-negative random variables on a probability space with $\mathbb E[\max_i X_i] < \infty$. Let $T = \tfrac12\mathbb E[\max_i X_i]$, $p = \Pr[\max_i X_i \ge T]$, and let $X_\tau$ be the reward of the rule that stops at the first $i$ with $X_i \ge T$ and collects $0$ if there is none. Then for all $x > T$,
--   $$\Pr[X_\tau > x] \;\ge\; (1-p)\,\Pr\big[\max_i X_i > x\big].$$
--
--   It compares the gambler's tail directly with the prophet's tail above the threshold: above $T$, the gambler's reward exceeds any level $x$ with at least a $(1-p)$ fraction of the probability that the prophet's value does.
--
--   **Formalization Note** Same conventions as the tail bound: `iIndepFun X P`, pointwise non-negativity, `Measure.real` probabilities; $T$, $p$, $X_\tau$ are defined from the data.
-- source:
--   Kleinberg & Weinberg, Matroid Prophet Inequalities, arXiv:1201.4764v1, p. 5, §3.1, display after "and therefore, for all x > T,"

import Mathlib
import Definitions.Def_MatroidProphetKW_RankOne_Setting

namespace MatroidProphetKW.RankOne

open MeasureTheory ProbabilityTheory

/-- §3.1, p. 5: for all `x > T`, `Pr[X_τ > x] ≥ (1 − p) Pr[max_i X_i > x]`. -/
theorem tail_bound_max
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} [NeZero n] (X : Fin n → Ω → ℝ)
    (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hnonneg : ∀ i ω, 0 ≤ X i ω) (hint : Integrable (maxX X) P)
    (x : ℝ) (hx : thr P X < x) :
    (1 - stopProb P X) * P.real {ω | x < maxX X ω} ≤ P.real {ω | x < reward P X ω} := by sorry

end MatroidProphetKW.RankOne
