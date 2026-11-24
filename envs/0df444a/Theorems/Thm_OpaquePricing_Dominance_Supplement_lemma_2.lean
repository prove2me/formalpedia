-- Prove2me | Theorems.Thm_OpaquePricing_Dominance_Supplement_lemma_2
-- name    : OpaquePricing.Dominance.Supplement.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T23:36:03.762206+00:00
-- url     : https://prove2.me/theorems/11b80bdd-1822-4f15-af6b-bcf9f3fef39d
-- title:
--   Lemma 2 — Pessimistic i.i.d. opaque revenue bound
-- statement:
--   Let $N\ge2$ items have i.i.d. nonnegative valuations with common Borel probability law $\nu$. When every customer is pessimistic,
--   $$R_{OPQ}(\nu^{\otimes N},1)\le3R_{SP}(\nu^{\otimes N}).$$
--   This is the pessimistic endpoint bound used by Theorem 2. No restriction on atoms, support, or mean is imposed.
--
--   Differences from the source:
--   - encoding: items 1 through N with N at least 2 → Fin N with the explicit premise 2 ≤ N; reason: zero-based indices preserve the full selling-model domain
--   - encoding: i.i.d. nonnegative item valuations → the finite product of one Borel probability measure with almost surely nonnegative values; reason: represents every i.i.d. law, including atoms and unbounded tails
--   - encoding: nonnegative prices, expected revenues, and optimal prices → published highest-price choice revenue, nonnegative real prices, and ENNReal expectations and suprema; reason: preserves atomic and unbounded laws without an integrability or attained-optimum premise; the inherited supremum convention is disclosed in the published base mission
-- source:
--   Elmachtoub & Hamilton, The Power of Opaque Products in Pricing, author's manuscript (2021; Manag. Sci. doi:10.1287/mnsc.2020.3750), Lemma 2, p. 45

import Mathlib
import Definitions.Def_OpaquePricing_Dominance_Setting
import Definitions.Def_OpaquePricing_Dominance_Supplement_SinglePricing

open MeasureTheory

namespace OpaquePricing.Dominance.Supplement

theorem lemma_2 {N : ℕ} (hN : 2 ≤ N) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ x ∂ν, 0 ≤ x) :
    optOPQ (Measure.pi (fun _ : Fin N => ν)) 1 ≤
      3 * optSP (Measure.pi (fun _ : Fin N => ν)) := by sorry

end OpaquePricing.Dominance.Supplement
