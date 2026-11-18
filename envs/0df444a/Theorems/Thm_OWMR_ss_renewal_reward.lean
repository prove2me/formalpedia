-- Prove2me | Theorems.Thm_OWMR_ss_renewal_reward
-- name    : OWMR.ss_renewal_reward
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-16T02:42:38.78537+00:00
-- url     : https://prove2.me/theorems/6bdb5b5e-b5e1-4ce3-9378-9ea05d8b8f89
-- title:
--   Occupation identity (10) for an $(s,S)$ policy started at $S$
-- statement:
--   Let demands be i.i.d. with law $\rho$ on $[0,\infty)$ and positive mean, and let $U$ be the renewal measure and $M(w)=U[0,w)$. Let $f:\mathbb R\to[0,\infty)$ be measurable and bounded above on $[s,S]$, where $s<S$, and let $K\ge0$. Consider the $(s,S)$ policy started at position $S$: whenever its position is at most $s$ it orders up to $S$, paying $K$, and every period it pays $f$ at its post-order position. Its long-run average expected cost (a $\limsup$ of time averages) equals
--
--   $$\frac{K+\displaystyle\int_{[0,S-s)}f(S-x)\,U(dx)}{M(S-s)} .$$
--
--   This is the occupation identity (10) of the source, $\mathbb E\,v(X_w)=M(w)^{-1}\int_{[0,w)}v\,dU$, applied to $v(x)=f(S-x)$, together with the order frequency $1/M(w)$ of the width-$w=S-s$ policy; it follows from the renewal-reward theorem for expected time averages, since the policy has i.i.d. cycles whose post-order depletions are $D^{(0)},\ldots,D^{(\tau_w-1)}$ with $\tau_w=\inf\{n\ge1:D^{(n)}\ge w\}$.
--
--   **Formalization Note** The average cost is `ssAvgCost ρ f K s S`, an extended nonnegative real; the right side is real and is embedded by `ENNReal.ofReal`.
-- source:
--   M. Hu, "A 5/2 Guarantee for Echelon Stock (s,S) Policies in One-Warehouse Multi-Retailer Systems", working paper (manuscript of November 2026), Section 4.2, eq. (10) and the renewal-reward argument stated before it, p. 13; in this form it is eq. (13) of Lemma 3, p. 14, and the first two terms of the candidate cost (15) in Lemma 4, p. 15.

import Definitions.Def_owmr_renewal

open MeasureTheory
open scoped ENNReal NNReal

namespace OWMR
theorem ss_renewal_reward (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ]
    (hρ : 0 < ∫⁻ x, (x : ℝ≥0∞) ∂ρ) (f : ℝ → ℝ) (hf : Measurable f) (hf0 : ∀ y, 0 ≤ f y)
    (K s S : ℝ) (hK : 0 ≤ K) (hsS : s < S) (hfb : ∃ C, ∀ y ∈ Set.Icc s S, f y ≤ C) :
    ssAvgCost ρ f K s S
      = ENNReal.ofReal ((K + ∫ x in Set.Ico 0 (S - s), f (S - x) ∂(renewalMeasure ρ))
          / (renewalMeasure ρ (Set.Ico 0 (S - s))).toReal) := by sorry
end OWMR
