-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_integral_truncated_real_concaveOn
-- name    : NestedSeatAlloc.IntPolicy.integral_truncated_real_concaveOn
-- status  : Open
-- author  : @WillR
-- created : 2026-10-06T16:13:40.492969+00:00
-- url     : https://prove2.me/theorems/5319f63e-bfd6-4b26-a2fc-273a8d1f23ba
-- title:
--   Expectation preserves concavity of a real-demand truncation
-- statement:
--   Under pointwise concavity and integrability of every nonnegative slice, the Bochner expectation of a real-demand truncated payoff is concave on the nonnegative ray.
-- source:
--   Source-faithful real-valued expectation concavity bridge in candidates/eq27_integral_truncated_real_concaveOn.lean; this is the concavity half of equation (27).

import Mathlib

namespace NestedSeatAlloc.IntPolicy

open MeasureTheory

theorem integral_truncated_real_concaveOn
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (a : ℝ) (N : Ω → ℝ)
    (hconc : ∀ᵐ ω ∂P,
      ConcaveOn ℝ (Set.Ici 0) (fun s : ℝ => a * min s (N ω)))
    (hint : ∀ s ∈ Set.Ici (0 : ℝ),
      Integrable (fun ω => a * min s (N ω)) P) :
    ConcaveOn ℝ (Set.Ici 0)
      (fun s : ℝ => ∫ ω, a * min s (N ω) ∂P) := by sorry

end NestedSeatAlloc.IntPolicy
