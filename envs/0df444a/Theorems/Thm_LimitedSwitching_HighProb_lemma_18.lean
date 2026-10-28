-- Prove2me | Theorems.Thm_LimitedSwitching_HighProb_lemma_18
-- name    : LimitedSwitching.HighProb.lemma_18
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:14:13.61098+00:00
-- url     : https://prove2.me/theorems/8d576e20-0f00-4446-a27f-1f45376260e6
-- title:
--   Lemma 18, p. 28 — the maximum X of n i.i.d. standard exponentials satisfies E[e^{tX}] ≤ n^t/(1 − t) for t ∈ (0, 1)
-- statement:
--   Let $n\ge1$ and let $X=\max_{i\in[n]}R(i)$, where $R(1),\dots,R(n)$ are i.i.d. standard exponential random variables. Then for every $t\in(0,1)$,
--
--   $$\mathbb E\big[e^{tX}\big]\le\frac{n^t}{1-t}.$$
--
--   This moment-generating-function bound is the input of the Chernoff argument for Lemma 9.
--
--   **Formalization Note** The expectation is a lower Lebesgue integral in $[0,\infty]$, so it is the true expectation and integrability is not presupposed. At $n=1$ the bound holds with equality.
-- source:
--   Altschuler & Talwar, Online learning over a finite action set with limited switching, arXiv:1803.01548v2, p. 28, Appendix D, Lemma 18

import Mathlib
import Definitions.Def_LimitedSwitching_HighProb_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LimitedSwitching.HighProb

theorem lemma_18 {n : ℕ} [NeZero n] (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    ∫⁻ R, ENNReal.ofReal (Real.exp (t * Finset.univ.sup' Finset.univ_nonempty R)) ∂(expLaw n)
      ≤ ENNReal.ofReal ((n : ℝ) ^ t / (1 - t)) := by sorry

end LimitedSwitching.HighProb
