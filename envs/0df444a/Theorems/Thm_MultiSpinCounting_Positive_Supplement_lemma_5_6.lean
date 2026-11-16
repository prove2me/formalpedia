-- Prove2me | Theorems.Thm_MultiSpinCounting_Positive_Supplement_lemma_5_6
-- name    : MultiSpinCounting.Positive.Supplement.lemma_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:27:23.951039+00:00
-- url     : https://prove2.me/theorems/b5ed6c3b-b322-4149-a290-05273549ff91
-- title:
--   Lemma 5.6 (used in the proof of Theorem 1.7) — zero-extension contraction
-- statement:
--   Let $\Omega_+$ be a nonempty subset of a finite state space $\Omega$. Let $p,p'$ be probability vectors strictly positive on $\Omega_+$ and zero outside it. For real $s\ge2$, suppose every coordinate of each vector on $\Omega_+$ is at most $1/s$. Then for every $a,b\in\Omega$, including coordinates absent from the support,
--   $$\left|\log\frac{1-p_a}{1-p'_a}-\log\frac{1-p_b}{1-p'_b}\right|\le\frac{d_{H,\Omega_+}(p,p')}{s-1}.$$
--   The Hilbert distance uses only $\Omega_+$, whereas $a$ and $b$ range over the full space. This is the contraction estimate for list-coloring marginal ratios.
--
--   Differences from the source:
--   - encoding: arbitrary finite state space → a finite interval or a finite subset of a finite interval; reason: bijections preserve every vector, sum, maximum and probability
-- source:
--   Zhidan Li, Kuan Yang, STOC 2027 submission #268 (October 2026), p. 22, Lemma 5.6

import Mathlib
import Definitions.Def_MultiSpinCounting_Positive_Supplement_Metrics

namespace MultiSpinCounting.Positive.Supplement

/-- Lemma 5.6, p. 22: a and b may be outside the positive common support. -/
theorem lemma_5_6 {N : ℕ} (S : Finset (Fin N)) (hS : S.Nonempty)
    (p p' : Fin N → ℝ) (s : ℝ) (hs : 2 ≤ s)
    (hp : ∀ a ∈ S, 0 < p a) (hp' : ∀ a ∈ S, 0 < p' a)
    (hz : ∀ a, a ∉ S → p a = 0) (hz' : ∀ a, a ∉ S → p' a = 0)
    (hn : ∑ a, p a = 1) (hn' : ∑ a, p' a = 1)
    (hb : ∀ a ∈ S, p a ≤ 1 / s) (hb' : ∀ a ∈ S, p' a ≤ 1 / s) :
    ∀ a b : Fin N,
      |Real.log ((1 - p a) / (1 - p' a)) -
        Real.log ((1 - p b) / (1 - p' b))| ≤ supportHilbert S p p' / (s - 1) := by sorry

end MultiSpinCounting.Positive.Supplement
