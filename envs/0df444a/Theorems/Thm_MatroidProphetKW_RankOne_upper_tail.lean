-- Prove2me | Theorems.Thm_MatroidProphetKW_RankOne_upper_tail
-- name    : MatroidProphetKW.RankOne.upper_tail
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:25:02.976309+00:00
-- url     : https://prove2.me/theorems/bbc9dcc3-ae4a-4da4-8d20-bd7c7319f9fd
-- title:
--   §3.1, p. 5 — ∫_T^∞ Pr[max_i X_i > x] dx ≥ T
-- statement:
--   Let $X_1,\dots,X_n$ ($n\ge1$) be independent, non-negative random variables on a probability space with $\mathbb E[\max_i X_i] < \infty$, and let $T = \tfrac12\mathbb E[\max_i X_i]$. Then
--   $$\int_T^\infty \Pr\big[\max_i X_i > x\big]\,dx \;\ge\; T.$$
--
--   It says that at least half of the prophet's expected value $\mathbb E[\max_i X_i] = 2T$ comes from the part of the distribution of $\max_i X_i$ above the threshold $T$; this is the half of the prophet's value that the gambler's tail bound is compared with.
--
--   **Formalization Note** The integral is the Lebesgue (Bochner) integral of $x \mapsto \mathbb P(\max_i X_i > x)$ over the open half-line $(T,\infty)$; if that function were not integrable the integral would be $0$ and the statement would fail for $T > 0$, so the statement includes the integrability. The independence and non-negativity hypotheses are the section's standing assumptions; the independence is not needed for this step.
-- source:
--   Kleinberg & Weinberg, Matroid Prophet Inequalities, arXiv:1201.4764v1, p. 5, §3.1, sentence after "Now, observe that"

import Mathlib
import Definitions.Def_MatroidProphetKW_RankOne_Setting

namespace MatroidProphetKW.RankOne

open MeasureTheory ProbabilityTheory

/-- §3.1, p. 5: `∫_T^∞ Pr[max_i X_i > x] dx ≥ T`, where `T = E[max_i X_i]/2`. -/
theorem upper_tail
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} [NeZero n] (X : Fin n → Ω → ℝ)
    (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hnonneg : ∀ i ω, 0 ≤ X i ω) (hint : Integrable (maxX X) P) :
    thr P X ≤ ∫ x in Set.Ioi (thr P X), P.real {ω | x < maxX X ω} := by sorry

end MatroidProphetKW.RankOne
