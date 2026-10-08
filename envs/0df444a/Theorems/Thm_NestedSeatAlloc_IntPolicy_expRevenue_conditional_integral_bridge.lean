-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_expRevenue_conditional_integral_bridge
-- name    : NestedSeatAlloc.IntPolicy.expRevenue_conditional_integral_bridge
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T18:23:28.204673+00:00
-- url     : https://prove2.me/theorems/103e58a3-6bcb-47d6-960e-41db0578fa86
-- title:
--   Expected revenue as the conditional-revenue integral
-- statement:
--   For a probability seat model and nonnegative capacity, expected revenue after adding the next fare class equals the integral of the fixed-demand conditional revenue against the law of that class's demand.
-- source:
--   Source-faithful expectation bridge required by the Open mission theorem NestedSeatAlloc.IntPolicy.corollary1_integrate_conditional_concavity (4204a6a5-95d4-4ce8-a739-2e52d3e9523a). Independence of the next demand from the finite prefix yields the product-law decomposition of the pair pushforward; integrability follows from the published finite-fare revenue envelope, and product integration followed by the definition of condRevenue gives this identity. The existing parent candidate implements this bridge but is rejected by E150 because the proof is one oversized declaration; this child isolates that genuine measure-theoretic subclaim instead of splitting syntax or asserting an unrelated helper.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

namespace NestedSeatAlloc.IntPolicy

open MeasureTheory ProbabilityTheory

theorem expRevenue_conditional_integral_bridge {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ)
    (hM : IsSeatModel P X f) (hp : IsProtectionPolicy p)
    (k : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    expRevenue P X f p (k + 1) s =
      ∫ y, condRevenue P X f p (k + 1) y s ∂Measure.map (X (k + 1)) P := by sorry

end NestedSeatAlloc.IntPolicy
