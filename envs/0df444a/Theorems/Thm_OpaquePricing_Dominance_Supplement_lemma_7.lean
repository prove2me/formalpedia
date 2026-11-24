-- Prove2me | Theorems.Thm_OpaquePricing_Dominance_Supplement_lemma_7
-- name    : OpaquePricing.Dominance.Supplement.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T23:39:15.556249+00:00
-- url     : https://prove2.me/theorems/18d02c5e-43a0-485f-8ad6-717e80746959
-- title:
--   Lemma 7 — Weighted tail ratio and harmonic bound
-- statement:
--   Let $N\ge2$, $x_1,\ldots,x_{N-1}\ge0$, $\sum_i x_i\le1$ and $C\ge0$. Then
--   $$\frac{1+C\sum_{i=1}^{N-1}ix_i}{1+C\max_{1\le i\le N-1}i\sum_{k=i}^{N-1}x_k}\le\frac{1+CH_{N-1}}{1+C}.$$
--   This inequality supplies the weighted-tail bound used in the proof of Theorem 4. Every coordinate, including the last tail term, is included.
--
--   Differences from the source:
--   - encoding: items 1 through N with N at least 2 → Fin N with the explicit premise 2 ≤ N; reason: zero-based indices preserve the full selling-model domain
--   - encoding: one-based indices 1 through N−1 → Fin (N−1), weight i.val+1 and the inclusive tail i≤k; reason: N≥2 makes the range nonempty; both denominators are positive, and adding zero to the maximum changes no value
-- source:
--   Elmachtoub & Hamilton, The Power of Opaque Products in Pricing, author's manuscript (2021; Manag. Sci. doi:10.1287/mnsc.2020.3750), Lemma 7, p. 53

import Mathlib
import Definitions.Def_OpaquePricing_Dominance_Setting
import Definitions.Def_OpaquePricing_Dominance_Supplement_Harmonic

open MeasureTheory

namespace OpaquePricing.Dominance.Supplement

theorem lemma_7 {N : ℕ} (hN : 2 ≤ N) (x : Fin (N - 1) → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hsum : ∑ i, x i ≤ 1) (C : ℝ) (hC : 0 ≤ C) :
    (1 + C * ∑ i, ((i.val : ℝ) + 1) * x i) / (1 + C * weightedTailMax x) ≤
      (1 + C * harmonic (N - 1)) / (1 + C) := by sorry

end OpaquePricing.Dominance.Supplement
