-- Prove2me | Theorems.Thm_OpaquePricing_Dominance_Supplement_lemma_9
-- name    : OpaquePricing.Dominance.Supplement.lemma_9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T23:41:19.935382+00:00
-- url     : https://prove2.me/theorems/a5d60f0d-80b7-4191-ac09-52ccb94dea80
-- title:
--   Lemma 9 — Risk-neutral customers in E₂ buy the opaque product
-- statement:
--   Let $N\ge2$, let $v\in\mathbb R_{\ge0}^N$, and let $p,r$ be the common item price and full-set opaque price, with $0\le r<p/N$. Suppose
--   $$p\le\max_i v_i<\frac{N}{N-1}(p-r).$$
--   For a risk-neutral customer the full-set opaque option has nonnegative utility strictly greater than every item utility, and the customer pays $r$:
--   $$0\le\frac1N\sum_i v_i-r,\qquad v_i-p<\frac1N\sum_kv_k-r\ (i=1,\ldots,N),\qquad \operatorname{rev}_{1OPQ}=r.$$
--   This is the Case 2 purchase statement used in Theorem 5, with the precise half-open region of p. 51.
--
--   Differences from the source:
--   - encoding: items 1 through N with N at least 2 → Fin N with the explicit premise 2 ≤ N; reason: zero-based indices preserve the full selling-model domain
--   - encoding: a customer in E₂ buys the opaque product, in risk-neutral Case 2 → the inherited nonnegative valuations, 0≤r<p/N, the half-open E₂ region, and strict utility and payment conclusions; reason: the assumptions and strict preference are stated explicitly in the p. 51 context and p. 54 proof; no optimal-price premise is needed
--   - generalization: optimal prices (p,p^N) in the inherited Case 2 context on p. 51 → every pair of prices with 0≤r<p/N, whether optimal or not; reason: the pointwise inequalities in the proof on p. 54 use only the price range, nonnegative valuations and membership in E₂; specializing to optimal prices recovers the source claim
-- source:
--   Elmachtoub & Hamilton, The Power of Opaque Products in Pricing, author's manuscript (2021; Manag. Sci. doi:10.1287/mnsc.2020.3750), Lemma 9, p. 54

import Mathlib
import Definitions.Def_OpaquePricing_Dominance_Setting
import Definitions.Def_OpaquePricing_Dominance_Supplement_OneOpaque
import Definitions.Def_OpaquePricing_Dominance_Supplement_PurchaseRegion

open MeasureTheory

namespace OpaquePricing.Dominance.Supplement

theorem lemma_9 {N : ℕ} (hN : 2 ≤ N) (v : Fin N → ℝ)
    (hv : ∀ i, 0 ≤ v i) (p r : ℝ) (hr : 0 ≤ r) (hsmall : r < p / N)
    (hE : v ∈ E2 p r) :
    0 ≤ rnValue v Finset.univ - r ∧
    (∀ i, v i - p < rnValue v Finset.univ - r) ∧
    oneRevenue rnValue p r v = r := by sorry

end OpaquePricing.Dominance.Supplement
