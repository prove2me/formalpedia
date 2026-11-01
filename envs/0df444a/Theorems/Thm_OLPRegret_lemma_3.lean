-- Prove2me | Theorems.Thm_OLPRegret_lemma_3
-- name    : OLPRegret.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:04:36.84454+00:00
-- url     : https://prove2.me/theorems/e7121716-7583-48b2-9e96-c84423e6e8ce
-- title:
--   Lemma 3 — inventory concentrates under Algorithm 2
-- statement:
--   Under Assumptions 2–6 and Algorithm 2, for every $\delta>0$ there are $C>0$ and $T$ such that for all $n$ and all $t$ with $T\le t\le n$,
--   $$
--   \Pr(b_t\notin B_\delta(\beta))\le\exp(-Ct).
--   $$
--
--   Differences from the source:
--   - reading: $y_\infty^{b}$ in Algorithm 2, which Lemma 2 defines only near $\beta$ → any selection $y$ that minimizes $\Lambda_\infty^b$ for $b$ near $\beta$ and is arbitrary elsewhere; reason: the page does not define $y_\infty^b$ far from $\beta$; the bound holds for every such selection
--   - encoding: "for all sufficiently large $t$" → a threshold $T$ and a constant $C$ uniform in the horizon $n$; reason: the bound (43) in the proof is uniform in $n$
--   - encoding: $\Pr$ → a measure of a possibly non-measurable set, which is the outer measure; reason: only strengthens the bound; the set is measurable for a measurable selection
-- source:
--   Bray, arXiv:1912.08917v6, Lemma 3, p.25; bound (43), Online Appendix p.10

import Mathlib
import Definitions.Def_OLPRegret_algorithm2

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal Topology

namespace OLPRegret

/-- Bray, arXiv:1912.08917v6, Lemma 3, p.25: under Algorithm 2, for all `δ > 0` there exists `C > 0`
such that `Pr(bₜ ∉ B_δ(β)) ≤ exp(−Ct)`, for all sufficiently large `t`.

**Formalization Note** `C` and the threshold do not depend on the horizon `n` (the proof's bound (43),
Online Appendix p.10, is uniform in `n`). `y` is any selection equal to `y∞ᵇ` near `β`. If that
selection is not measurable the probability is the outer measure, which only strengthens the bound. -/
theorem lemma_3 {m : ℕ} (μ : Measure (Customer m)) [IsProbabilityMeasure μ] (β : E m)
    (hβ : VNonneg β) (hA : Assumptions μ β) (y : E m → E m) (hy : IsLimitPrice μ β y)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ, ∀ n t : ℕ, T ≤ t → t ≤ n →
      sampleLaw μ n {ω | inventory (algorithm2 y) β ω t ∉ Metric.ball β δ} ≤
        ENNReal.ofReal (Real.exp (-C * t)) := by sorry

end OLPRegret
