-- Prove2me | Theorems.Thm_OpaquePricing_Dominance_Supplement_theorem_2
-- name    : OpaquePricing.Dominance.Supplement.theorem_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T23:37:15.788147+00:00
-- url     : https://prove2.me/theorems/52bae622-e108-4291-aaf6-cb9ee4a53ec7
-- title:
--   Theorem 2 — I.i.d. opaque versus single-pricing bound
-- statement:
--   Let $N\ge2$, let the item valuations have common nonnegative Borel probability law $\nu$ and be independent, and let $\alpha\in[0,1]$ be the pessimistic fraction of customers. Then
--   $$R_{OPQ}(\nu^{\otimes N},\alpha)\le\left(3+(1-\alpha)\left(1-\frac2N\right)\right)R_{SP}(\nu^{\otimes N}).$$
--   The result bounds the advantage of offering every opaque subset against a single item price. It assumes neither a finite mean nor an attained optimum.
--
--   Differences from the source:
--   - encoding: items 1 through N with N at least 2 → Fin N with the explicit premise 2 ≤ N; reason: zero-based indices preserve the full selling-model domain
--   - encoding: i.i.d. nonnegative item valuations → the finite product of one Borel probability measure with almost surely nonnegative values; reason: represents every i.i.d. law, including atoms and unbounded tails
--   - encoding: a pessimistic fraction α and a risk-neutral fraction 1−α → α ∈ [0,1] and the published independent mixture; reason: makes the probability range explicit and does not replace a mixture of revenues by a mixture of valuations
--   - encoding: nonnegative prices, expected revenues, and optimal prices → published highest-price choice revenue, nonnegative real prices, and ENNReal expectations and suprema; reason: preserves atomic and unbounded laws without an integrability or attained-optimum premise; the inherited supremum convention is disclosed in the published base mission
-- source:
--   Elmachtoub & Hamilton, The Power of Opaque Products in Pricing, author's manuscript (2021; Manag. Sci. doi:10.1287/mnsc.2020.3750), Theorem 2, p. 21

import Mathlib
import Definitions.Def_OpaquePricing_Dominance_Setting
import Definitions.Def_OpaquePricing_Dominance_Supplement_SinglePricing

open MeasureTheory

namespace OpaquePricing.Dominance.Supplement

theorem theorem_2 {N : ℕ} (hN : 2 ≤ N) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ x ∂ν, 0 ≤ x) (α : ℝ) (hα : α ∈ Set.Icc 0 1) :
    optOPQ (Measure.pi (fun _ : Fin N => ν)) α ≤
      ENNReal.ofReal (3 + (1 - α) * (1 - 2 / (N : ℝ))) *
        optSP (Measure.pi (fun _ : Fin N => ν)) := by sorry

end OpaquePricing.Dominance.Supplement
