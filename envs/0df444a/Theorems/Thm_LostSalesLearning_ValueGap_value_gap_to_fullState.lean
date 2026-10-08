-- Prove2me | Theorems.Thm_LostSalesLearning_ValueGap_value_gap_to_fullState
-- name    : LostSalesLearning.ValueGap.value_gap_to_fullState
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T10:18:48.208816+00:00
-- url     : https://prove2.me/theorems/bc318c54-5d40-41c7-ac6a-65d7e85db765
-- title:
--   Proof of Lemma 2.5, p. 9 — |V^x_T(s) − V^x_T(ŝ)| ≤ 9(h + p)Lx for every s ∈ S^x, ŝ = (x, 0, …, 0)
-- statement:
--   Consider the base-stock lost-sales Markov reward process with lead time $L\ge 1$, base-stock level $x$, holding cost $h\ge 0$ and lost-sales penalty $p\ge 0$ per unit, and i.i.d. demands with an arbitrary law $F$ on $[0,\infty)$. Let $V^x_T(\mathbf s)$ be its value over horizon $T$ from the start state $\mathbf s$, and let $\hat{\mathbf s}=(x,0,\dots,0)$. Then for every $\mathbf s\in\mathcal S^x$ and every $T$,
--   $$\big|V^x_T(\mathbf s)-V^x_T(\hat{\mathbf s})\big|\le 9(h+p)Lx .$$
--
--   This is the step of the proof of Lemma 2.5 where the pathwise bounds of Lemmas B.6 and B.7 pass to expectations: the value is $\mathbb E[h\,m^x_T(\mathbf s)-(h+p)\,n^x_T(\mathbf s)]$, so the difference of values is one expectation of the difference along a common demand path. Applying it to two states $\mathbf s,\mathbf s'$ through $\hat{\mathbf s}$ gives Lemma 2.5.
--
--   **Formalization Note** The value is the expectation of the summed pseudo-costs under the product law of the demand path, the form used on p. 8. The costs $h,p$ are nonnegative, the reading of "per unit holding cost and per unit lost sales penalty" in §1.1. No assumption is placed on $F$ beyond being a probability law on $[0,\infty)$. The hypothesis $L\ge 1$ is that of Appendix B, on which the step rests.
-- source:
--   Agrawal & Jia, Learning in Structured MDPs with Convex Cost Functions, arXiv:1905.04337v1, p. 9, proof of Lemma 2.5, second display

import Mathlib
import Definitions.Def_LostSalesLearning_ValueGap_Setting

open MeasureTheory
open scoped NNReal

namespace LostSalesLearning.ValueGap

theorem value_gap_to_fullState {L : ℕ} (hL : 1 ≤ L) (h p x : ℝ) (hh : 0 ≤ h) (hp : 0 ≤ p)
    (F : Measure ℝ≥0) [IsProbabilityMeasure F] (T : ℕ) (s : Fin (L + 1) → ℝ)
    (hs : s ∈ Sx L x) :
    |value h p F T s - value h p F T (fullState L x)| ≤ 9 * (h + p) * (L : ℝ) * x := by sorry

end LostSalesLearning.ValueGap
