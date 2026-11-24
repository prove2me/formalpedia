-- Prove2me | Theorems.Thm_OpaquePricing_Dominance_Supplement_lemma_4
-- name    : OpaquePricing.Dominance.Supplement.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T23:36:44.812477+00:00
-- url     : https://prove2.me/theorems/d5f711ac-4bf1-4420-ac7a-84295903ee55
-- title:
--   Lemma 4 — Risk-neutral i.i.d. opaque revenue bound
-- statement:
--   Let $N\ge2$ items have i.i.d. nonnegative valuations with common Borel probability law $\nu$. When every customer is risk-neutral,
--   $$R_{OPQ}(\nu^{\otimes N},0)\le\left(4-\frac2N\right)R_{SP}(\nu^{\otimes N}).$$
--   This is the risk-neutral endpoint bound used by Theorem 2. Arbitrary atoms and unbounded tails remain in scope.
--
--   Differences from the source:
--   - encoding: items 1 through N with N at least 2 → Fin N with the explicit premise 2 ≤ N; reason: zero-based indices preserve the full selling-model domain
--   - encoding: i.i.d. nonnegative item valuations → the finite product of one Borel probability measure with almost surely nonnegative values; reason: represents every i.i.d. law, including atoms and unbounded tails
--   - encoding: nonnegative prices, expected revenues, and optimal prices → published highest-price choice revenue, nonnegative real prices, and ENNReal expectations and suprema; reason: preserves atomic and unbounded laws without an integrability or attained-optimum premise; the inherited supremum convention is disclosed in the published base mission
-- source:
--   Elmachtoub & Hamilton, The Power of Opaque Products in Pricing, author's manuscript (2021; Manag. Sci. doi:10.1287/mnsc.2020.3750), Lemma 4, p. 45

import Mathlib
import Definitions.Def_OpaquePricing_Dominance_Setting
import Definitions.Def_OpaquePricing_Dominance_Supplement_SinglePricing

open MeasureTheory

namespace OpaquePricing.Dominance.Supplement

theorem lemma_4 {N : ℕ} (hN : 2 ≤ N) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ x ∂ν, 0 ≤ x) :
    optOPQ (Measure.pi (fun _ : Fin N => ν)) 0 ≤
      ENNReal.ofReal (4 - 2 / (N : ℝ)) * optSP (Measure.pi (fun _ : Fin N => ν)) := by sorry

end OpaquePricing.Dominance.Supplement
