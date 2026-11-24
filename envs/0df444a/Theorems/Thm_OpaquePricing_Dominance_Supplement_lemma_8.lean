-- Prove2me | Theorems.Thm_OpaquePricing_Dominance_Supplement_lemma_8
-- name    : OpaquePricing.Dominance.Supplement.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T23:40:37.528178+00:00
-- url     : https://prove2.me/theorems/4736818d-0c4a-4041-8acc-1c72c56a2f8b
-- title:
--   Lemma 8 — Full six-variable OPT bound
-- statement:
--   For $N\ge2$, let $OPT_N$ be the supremum of display (12), over all $a,b,c,d\ge0$ with $a+b+c+d=1$ and all real prices $x\ge y\ge x/N\ge0$. Then
--   $$\left[\exists z:\ D(z)>0,\quad OPT_N=\frac{x a+y(b+c)}{D(z)}\right],\qquad OPT_N\le2-\frac1N.$$
--   The supremum is attained at a feasible point with positive denominator, so it represents the source maximum. The ratio uses numerator $xa+y(b+c)$ and denominator $\max\{x(a+b),y(a+b+c)\}$. It includes the entire unnormalized feasible domain of the source optimization.
--
--   Differences from the source:
--   - encoding: items 1 through N with N at least 2 → Fin N with the explicit premise 2 ≤ N; reason: zero-based indices preserve the full selling-model domain
--   - reading: the maximum OPT of a homogeneous ratio → an ENNReal supremum over the positive-denominator feasible points, with attainment concluded in Lemma 8; reason: the existence of a maximizer is asserted rather than assumed; zero-denominator points have zero numerator and revenue, and the p. 54 proof supplies an attaining point x=1,y=a=1/N,b=d=0,c=1−1/N
-- source:
--   Elmachtoub & Hamilton, The Power of Opaque Products in Pricing, author's manuscript (2021; Manag. Sci. doi:10.1287/mnsc.2020.3750), Lemma 8, p. 53

import Mathlib
import Definitions.Def_OpaquePricing_Dominance_Setting
import Definitions.Def_OpaquePricing_Dominance_Supplement_Optimization

open MeasureTheory

namespace OpaquePricing.Dominance.Supplement

theorem lemma_8 {N : ℕ} (hN : 2 ≤ N) :
    (∃ z : RatioPoint N, 0 < ratioDen z ∧
      ENNReal.ofReal (ratioValue z) = optRatio N) ∧
    optRatio N ≤ ENNReal.ofReal (2 - 1 / (N : ℝ)) := by sorry

end OpaquePricing.Dominance.Supplement
