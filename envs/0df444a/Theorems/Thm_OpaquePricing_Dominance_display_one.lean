-- Prove2me | Theorems.Thm_OpaquePricing_Dominance_display_one
-- name    : OpaquePricing.Dominance.display_one
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:27:02.029647+00:00
-- url     : https://prove2.me/theorems/cb89fe37-8d70-4272-8b94-dd851515f206
-- title:
--   Proof of Theorem 1, display (1): mixed DP revenue conditional on high-value count
-- statement:
--   Suppose $N\ge2$, $0\le a<b$, and an exchangeable valuation law is supported on $\{a,b\}^N$. Price one item at $a$ and the others at $b$. If $U$ counts coordinates equal to $b$, then for each $1\le i\le N$ the contribution from $U=i$ to expected revenue is
--
--   $$\mathbb E[R_{\mathrm{DP}}\mathbf 1_{\{U=i\}}]=\left(a+\frac{N-i}{N}(b-a)\right)\Pr(U=i).$$
--
--   When $\Pr(U=i)>0$, this gives the corresponding conditional expected revenue. It is the unnormalized version of display (1).
--
--   **Formalization Note** The equation remains meaningful when $\Pr(U=i)=0$ and avoids division by a zero event probability.
-- source:
--   Elmachtoub & Hamilton, The Power of Opaque Products in Pricing, author's manuscript (2021; Manag. Sci. doi:10.1287/mnsc.2020.3750), proof of Theorem 1, display (1), p. 19

import Mathlib
import Definitions.Def_OpaquePricing_Dominance_Setting

open MeasureTheory

namespace OpaquePricing.Dominance

theorem display_one {N : ℕ} (hN : 2 ≤ N)
    (μ : Measure (Fin N → ℝ)) [IsProbabilityMeasure μ]
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b)
    (hsupp : ∀ᵐ v ∂μ, ∀ i, v i = a ∨ v i = b)
    (hexch : Exchangeable μ) (i : ℕ) (hi0 : 1 ≤ i) (hiN : i ≤ N) :
    (∫⁻ v in {v | highCount b v = i},
      ENNReal.ofReal (dpRevenue (mixedPrice a b) v) ∂μ) =
      ENNReal.ofReal (a + (((N : ℝ) - i) / N) * (b - a)) *
        μ {v | highCount b v = i} := by sorry

end OpaquePricing.Dominance
