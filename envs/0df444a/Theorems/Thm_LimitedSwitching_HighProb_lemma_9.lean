-- Prove2me | Theorems.Thm_LimitedSwitching_HighProb_lemma_9
-- name    : LimitedSwitching.HighProb.lemma_9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:14:06.747459+00:00
-- url     : https://prove2.me/theorems/23ff197a-3243-4218-986a-15819e03333e
-- title:
--   Lemma 9, p. 14 — for i.i.d. standard exponentials, P(Σ_{e≤N} max_i R_e(i) > 6N log n) ≤ e^{−N}
-- statement:
--   Let $N,n\ge2$ be integers and let $\{R_e(i)\}_{e\in[N],\,i\in[n]}$ be i.i.d. standard exponential random variables. Then
--
--   $$\mathbb P\Big(\sum_{e=1}^{N}\max_{i\in[n]}R_e(i)>6N\log n\Big)\le e^{-N}.$$
--
--   The maximum of $n$ standard exponentials has mean about $\log n$. The lemma says that a sum of $N$ independent such maxima exceeds six times its order of magnitude only with exponentially small probability in $N$. In Theorem 8 it controls the total perturbation over the epochs.
--
--   **Formalization Note** The $N$ rows $R_e\in\mathbb R^n$ are indexed by $\mathrm{Fin}\,N$ under the product of $N$ copies of the $n$-fold exponential product law. The probability is the outer measure of the event.
-- source:
--   Altschuler & Talwar, Online learning over a finite action set with limited switching, arXiv:1803.01548v2, p. 14, Lemma 9; proof p. 29, Appendix D

import Mathlib
import Definitions.Def_LimitedSwitching_HighProb_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LimitedSwitching.HighProb

theorem lemma_9 {N n : ℕ} [NeZero n] (hN : 2 ≤ N) (hn : 2 ≤ n) :
    (Measure.pi (fun _ : Fin N => expLaw n))
        {R | 6 * (N : ℝ) * Real.log n < ∑ e, Finset.univ.sup' Finset.univ_nonempty (R e)}
      ≤ ENNReal.ofReal (Real.exp (-(N : ℝ))) := by sorry

end LimitedSwitching.HighProb
