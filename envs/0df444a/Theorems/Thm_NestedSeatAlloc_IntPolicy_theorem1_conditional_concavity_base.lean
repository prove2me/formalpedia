-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_theorem1_conditional_concavity_base
-- name    : NestedSeatAlloc.IntPolicy.theorem1_conditional_concavity_base
-- status  : Disproved
-- author  : @WillR
-- created : 2026-10-06T07:28:16.081482+00:00
-- url     : https://prove2.me/theorems/9c804232-0d6b-41f3-9455-609ca3df4889
-- title:
--   Theorem 1 concavity base — one-class conditional revenue is concave
-- statement:
--   For every nonnegative frozen demand value, the one-class conditional revenue function is concave on nonnegative seat levels.
-- source:
--   Source-faithful base case of Brumelle & McGill (1993), Theorem 1 conditional-concavity induction, pp. 131–132.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

namespace NestedSeatAlloc.IntPolicy

open MeasureTheory ProbabilityTheory

theorem theorem1_conditional_concavity_base {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ) (hM : IsSeatModel P X f)
    (hp : IsProtectionPolicy p) :
    ∀ y, 0 ≤ y → ConcaveOn ℝ (Set.Ici 0) (condRevenue P X f p 1 y) := by sorry

end NestedSeatAlloc.IntPolicy
