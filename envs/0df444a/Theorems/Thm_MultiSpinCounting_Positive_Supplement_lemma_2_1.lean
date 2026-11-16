-- Prove2me | Theorems.Thm_MultiSpinCounting_Positive_Supplement_lemma_2_1
-- name    : MultiSpinCounting.Positive.Supplement.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:25:32.749966+00:00
-- url     : https://prove2.me/theorems/076e7826-a716-4a5a-8fef-883d57aab584
-- title:
--   Lemma 2.1 (used in the proof of Theorem 1.2) — total variation from Hilbert distance
-- statement:
--   Let $p,p'$ be strictly positive probability vectors on the same nonempty finite state space $\Omega$: each coordinate is positive and each vector sums to one. Their total variation and Hilbert distances satisfy
--   $$\frac12\sum_{a\in\Omega}|p_a-p'_a|\le\tanh\!\left(\frac{d_H(p,p')}{4}\right)\le\frac{d_H(p,p')}{4}.$$
--   Both inequalities are asserted. This converts projective-metric control of positive marginal vectors into total-variation control.
--
--   Differences from the source:
--   - encoding: arbitrary finite state space → a finite interval or a finite subset of a finite interval; reason: bijections preserve every vector, sum, maximum and probability
-- source:
--   Zhidan Li, Kuan Yang, STOC 2027 submission #268 (October 2026), p. 8, Lemma 2.1

import Mathlib
import Definitions.Def_MultiSpinCounting_Positive_Supplement_Metrics

namespace MultiSpinCounting.Positive.Supplement

/-- Lemma 2.1, p. 8: both inequalities, for every finite nonempty state space. -/
theorem lemma_2_1 (k : ℕ) (hk : 0 < k) (p p' : Fin k → ℝ)
    (hp : ∀ a, 0 < p a) (hp' : ∀ a, 0 < p' a)
    (hn : ∑ a, p a = 1) (hn' : ∑ a, p' a = 1) :
    tvDist p p' ≤ Real.tanh (CompOT.Sinkhorn.hilbertMetric p p' / 4) ∧
    Real.tanh (CompOT.Sinkhorn.hilbertMetric p p' / 4) ≤
      CompOT.Sinkhorn.hilbertMetric p p' / 4 := by sorry

end MultiSpinCounting.Positive.Supplement
