-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_revenue_random_integrable_under_seat_model
-- name    : NestedSeatAlloc.IntPolicy.revenue_random_integrable_under_seat_model
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T18:03:40.247204+00:00
-- url     : https://prove2.me/theorems/5b65a6fd-a920-4de6-9f01-0f6ae9c28ab2
-- title:
--   Expected revenue integrability under the seat model
-- statement:
--   For every nonnegative capacity, revenue evaluated on the random demand sequence is integrable under the seat-model probability measure.
-- source:
--   Source-faithful analytic prerequisite for the open mission theorem NestedSeatAlloc.IntPolicy.corollary1_integrate_conditional_concavity (4204a6a5-95d4-4ce8-a739-2e52d3e9523a). The theorem packages the model-specific integrability proof obtained from the already-Proved finite-fare revenue envelope and joint measurability, and is used to transport integrability through the independent-pair pushforward via integrable_map_measure.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

namespace NestedSeatAlloc.IntPolicy

open MeasureTheory ProbabilityTheory

theorem revenue_random_integrable_under_seat_model {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ)
    (hM : IsSeatModel P X f) (hp : IsProtectionPolicy p)
    (n : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    Integrable (fun ω => revenue f p (fun i => X i ω) n s) P := by sorry

end NestedSeatAlloc.IntPolicy
