-- Prove2me | Theorems.Thm_MatroidProphetKW_RankOne_half_mean_threshold
-- name    : MatroidProphetKW.RankOne.half_mean_threshold
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:24:41.122162+00:00
-- url     : https://prove2.me/theorems/19b6f84f-0476-4df2-a621-a4b99aaf975c
-- title:
--   §3.1, p. 5 — stopping at the first X_τ ≥ E[max_i X_i]/2 gives E[X_τ] ≥ ½ E[max_i X_i]
-- statement:
--   Let $X_1,\dots,X_n$ ($n\ge1$) be independent, non-negative, real-valued random variables on a probability space with $\mathbb E[\max_i X_i] < \infty$. Let
--   $$T = \tfrac12\,\mathbb E\big[\max_i X_i\big],$$
--   and consider the online rule that observes $X_1, X_2, \dots$ in order, stops at the first time $\tau$ with $X_\tau \ge T$ and collects $X_\tau$, and collects $0$ if no $X_i$ reaches $T$. Then
--   $$\mathbb E[X_\tau] \;\ge\; T \;=\; \tfrac12\,\mathbb E\big[\max_i X_i\big].$$
--
--   This is the prophet inequality of Krengel, Sucheston and Garling, $2\,\mathbb E[X_\tau] \ge \mathbb E[\max_i X_i]$ (inequality (1) of the paper), proved for an explicit single-threshold rule: a gambler who sees the values one at a time and must decide irrevocably earns at least half of what a prophet who sees all values in advance earns. It is the rank-one case of the matroid prophet inequality of Kleinberg and Weinberg.
--
--   **Formalization Note** The variables are `X : Fin n → Ω → ℝ` with `[NeZero n]`, measurable, mutually independent (`iIndepFun`), pointwise non-negative, and with $\max_i X_i$ integrable. Expectations are Bochner integrals. The rule is the paper's rule, which may accept nothing; it is not forced to stop at $X_n$. The conclusion is stronger than (1)'s "there exists a stopping rule".
-- source:
--   Kleinberg & Weinberg, Matroid Prophet Inequalities, arXiv:1201.4764v1, p. 5, §3.1 (proof of (1), p. 1)

import Mathlib
import Definitions.Def_MatroidProphetKW_RankOne_Setting

namespace MatroidProphetKW.RankOne

open MeasureTheory ProbabilityTheory

/-- §3.1, p. 5: the rule that stops at the first `X_τ ≥ T = E[max_i X_i]/2` (and accepts nothing
if there is none) earns `E[X_τ] ≥ T = ½ E[max_i X_i]`; this proves the prophet inequality (1). -/
theorem half_mean_threshold
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} [NeZero n] (X : Fin n → Ω → ℝ)
    (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hnonneg : ∀ i ω, 0 ≤ X i ω) (hint : Integrable (maxX X) P) :
    (∫ ω, maxX X ω ∂P) / 2 ≤ ∫ ω, reward P X ω ∂P := by sorry

end MatroidProphetKW.RankOne
