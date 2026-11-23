-- Prove2me | Theorems.Thm_MaxSpectralRisk_Duality_Supplement_lemma_7
-- name    : MaxSpectralRisk.Duality.Supplement.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T10:11:30.898444+00:00
-- url     : https://prove2.me/theorems/234d1370-4a7e-4d43-815d-6e3a476643db
-- title:
--   Lemma 7 (used in the proof of Theorem 2) — normalizing a truncated density
-- statement:
--   Let $m$ be a probability measure, $A>1$, and $g\in L^\infty(m)$ with $0\le g\le A$ almost surely and $\int g\,dm=c\in(0,1)$. Set $\delta=A-1$ and suppose $\delta^2-4c(1-c)>0$. Then there exists a nonnegative shift $r$ such that
--   $$
--   \int\min(A,g+r)\,dm=1,\qquad
--   0\le r\le A-c-\frac{\delta+\sqrt{\delta^2-4c(1-c)}}2.
--   $$
--   This provides the quantitative normalization bound used for approximating bounded densities.
--
--   Differences from the source:
--   - encoding: g in L-infinity(m) and 0 ≤ g ≤ A → a representative f with MemLp f top and the bounds almost everywhere; reason: all source formulas depend only on the equivalence class and MemLp includes almost-everywhere strong measurability
-- source:
--   Ghossoub, Hall, Saunders, Maximum Spectral Measures of Risk with given Risk Factor Marginal Distributions, arXiv:2010.14673v1, p. 16, Lemma 7

import Mathlib

namespace MaxSpectralRisk.Duality.Supplement

open MeasureTheory

/-- Lemma 7, pp. 16–17. The whole (δ + sqrt(...)) is divided by 2.
The shift is nonnegative, as stipulated before the source's existence claim. -/
theorem lemma_7 {W : Type*} [TopologicalSpace W] [PolishSpace W]
    [MeasurableSpace W] [BorelSpace W]
    (m : ProbabilityMeasure W) (A c : ℝ) (f : W → ℝ)
    (hA : 1 < A) (hf : MemLp f ⊤ (m : Measure W))
    (hbound : ∀ᵐ w ∂(m : Measure W), 0 ≤ f w ∧ f w ≤ A)
    (hc : 0 < c ∧ c < 1) (hint : ∫ w, f w ∂(m : Measure W) = c)
    (hdisc : 0 < (A - 1) ^ 2 - 4 * c * (1 - c)) :
    ∃ r : ℝ, 0 ≤ r ∧
      r ≤ A - c - ((A - 1) + Real.sqrt ((A - 1) ^ 2 - 4 * c * (1 - c))) / 2 ∧
      (∫ w, min A (f w + r) ∂(m : Measure W)) = 1 := by sorry

end MaxSpectralRisk.Duality.Supplement
