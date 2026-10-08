-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_theorem1_conditional_concavity
-- name    : NestedSeatAlloc.IntPolicy.theorem1_conditional_concavity
-- status  : Open
-- author  : @WillR
-- created : 2026-10-05T23:34:35.497799+00:00
-- url     : https://prove2.me/theorems/8ce70da2-6c6b-4e95-9e6b-cfa89ea98f0a
-- title:
--   Theorem 1 concavity component — conditional revenue is concave under (20)
-- statement:
--   Under the nested seat model, if a protection policy satisfies the subdifferential condition (20), then for every nest index and nonnegative frozen demand value the corresponding conditional revenue function is concave on the nonnegative seats.
-- source:
--   Source-faithful decomposition of Brumelle–McGill (1993), Theorem 1, pp. 131–132: the conditional-concavity half of the theorem under condition (20).

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

namespace NestedSeatAlloc.IntPolicy

open MeasureTheory ProbabilityTheory

theorem theorem1_conditional_concavity {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ) (hM : IsSeatModel P X f) (hp : IsProtectionPolicy p)
    (h20 : SubdiffCondition P X f p) :
    ∀ k, 1 ≤ k → ∀ y, 0 ≤ y → ConcaveOn ℝ (Set.Ici 0) (condRevenue P X f p (k + 1) y) := by sorry

end NestedSeatAlloc.IntPolicy
