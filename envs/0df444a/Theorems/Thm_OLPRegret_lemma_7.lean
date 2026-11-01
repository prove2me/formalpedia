-- Prove2me | Theorems.Thm_OLPRegret_lemma_7
-- name    : OLPRegret.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:04:20.83002+00:00
-- url     : https://prove2.me/theorems/fb1c4cde-b9d9-42c7-95eb-d2ca229a89f8
-- title:
--   Lemma 7 — the optimal policy keeps inventory near $\beta$
-- statement:
--   Under Assumptions 2–6 and the Bellman policy, for every $\delta>0$ there is $N$ such that for all $n\ge N$ and all $t$ with $n^{3/4}\le t\le n/2$,
--   $$
--   \Pr(b_t\notin B_{\delta/2}(\beta))\le n^{-1/2}.
--   $$
--
--   Differences from the source:
--   - encoding: the optimal action (14) → `bellmanScheme`, ties rejected; reason: the page says "exceeds"
-- source:
--   Bray, arXiv:1912.08917v6, Lemma 7, p.30; proof Online Appendix pp.18–24 (PDF 54–60)

import Mathlib
import Definitions.Def_OLPRegret_bellmanValue

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal Topology

namespace OLPRegret

/-- Bray, arXiv:1912.08917v6, Lemma 7, p.30: under the optimal policy, for all `δ > 0`, if `n` is
sufficiently large then `n^{3/4} ≤ t ≤ n/2` implies `Pr(bₜ ∉ B_{δ/2}(β)) ≤ n^{−1/2}`. -/
theorem lemma_7 {m : ℕ} (μ : Measure (Customer m)) [IsProbabilityMeasure μ] (β : E m)
    (hβ : VNonneg β) (hA : Assumptions μ β) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ t : ℕ, (n : ℝ) ^ (3 / 4 : ℝ) ≤ t → (t : ℝ) ≤ n / 2 →
      sampleLaw μ n {ω | inventory (bellmanScheme μ) β ω t ∉ Metric.ball β (δ / 2)} ≤
        ENNReal.ofReal ((n : ℝ) ^ (-(1 / 2) : ℝ)) := by sorry

end OLPRegret
