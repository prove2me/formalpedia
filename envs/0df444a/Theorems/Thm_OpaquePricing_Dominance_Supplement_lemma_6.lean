-- Prove2me | Theorems.Thm_OpaquePricing_Dominance_Supplement_lemma_6
-- name    : OpaquePricing.Dominance.Supplement.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T23:37:51.288135+00:00
-- url     : https://prove2.me/theorems/c8aacd6d-4191-44b8-87f0-c7983c45a92c
-- title:
--   Lemma 6 — Weighted maximum ratio and harmonic bound
-- statement:
--   Let $N\ge2$, $x_1,\ldots,x_N\ge0$, $\sum_i x_i\le K$, and $C_1,C_2\ge0$. With $H_N=\sum_{i=1}^N1/i$,
--   $$\frac{C_1+C_2\sum_i x_i}{C_1+C_2\max_i ix_i}\le\frac{C_1+C_2KH_N}{C_1+C_2K}.$$
--   This weighted maximum inequality supports the discriminatory-pricing bound in Theorem 3. Every zero-constant case is included.
--
--   Differences from the source:
--   - encoding: items 1 through N with N at least 2 → Fin N with the explicit premise 2 ≤ N; reason: zero-based indices preserve the full selling-model domain
--   - encoding: one-based weights i and the maximum over nonnegative coordinates → Fin N weights i.val+1 and maxZero; reason: adding zero changes no maximum on the source domain
--   - reading: ratios with no declared zero-denominator convention → ordinary real division with 0/0=0; reason: a zero denominator forces its numerator to zero; the extension retains all nonnegative constants, including C₁=0 used in Theorem 3
-- source:
--   Elmachtoub & Hamilton, The Power of Opaque Products in Pricing, author's manuscript (2021; Manag. Sci. doi:10.1287/mnsc.2020.3750), Lemma 6, p. 52

import Mathlib
import Definitions.Def_OpaquePricing_Dominance_Setting
import Definitions.Def_OpaquePricing_Dominance_Supplement_Harmonic

open MeasureTheory

namespace OpaquePricing.Dominance.Supplement

/-- Real division is total: 0/0=0, preserving all zero-constant cases. -/
theorem lemma_6 {N : ℕ} (hN : 2 ≤ N) (x : Fin N → ℝ)
    (hx : ∀ i, 0 ≤ x i) (K C1 C2 : ℝ) (hK : ∑ i, x i ≤ K)
    (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) :
    (C1 + C2 * ∑ i, x i) / (C1 + C2 * weightedMax x) ≤
      (C1 + C2 * K * harmonic N) / (C1 + C2 * K) := by sorry

end OpaquePricing.Dominance.Supplement
