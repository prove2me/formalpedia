-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_condRevenue_one_concave_nonneg_fare
-- name    : NestedSeatAlloc.IntPolicy.condRevenue_one_concave_nonneg_fare
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T16:06:35.691068+00:00
-- url     : https://prove2.me/theorems/8f872bd0-29e0-4823-a429-99948c30d8e6
-- title:
--   Frozen first-class conditional revenue is concave when the first fare is nonnegative
-- statement:
--   For a probability model with a non-negative first fare, the
--   conditional revenue with frozen demand y equals f(1)*min(s,y).
--   The Proved condRevenue_one_frozen_formula establishes this
--   identity exactly. The minimum of capacity and fixed demand is
--   concave in capacity; a nonnegative multiplier preserves concavity.
--
--   The Lean proof constructs ConcaveOn explicitly. The minimum
--   inequality is verified by bounding each minimum by capacity
--   and demand, using nonnegative convex weights and the weights
--   summing to one. It then multiplies the result by f(1)>=0.
--   The theorem does not assume integer demands or y>=0.
--
--   The original theorem1_conditional_concavity_base is Disproved
--   because it failed to assume f(1)>=0. This is the corrected
--   conditional base, not a proof of the full general Theorem 1
--   (which has to derive any needed positivity from condition (20)).
--   Only Prove2Me remote compilation is authoritative.
-- source:
--   For a probability model with a non-negative first fare, the
--   conditional revenue with frozen demand y equals f(1)*min(s,y).
--   The Proved condRevenue_one_frozen_formula establishes this
--   identity exactly. The minimum of capacity and fixed demand is
--   concave in capacity; a nonnegative multiplier preserves concavity.
--
--   The Lean proof constructs ConcaveOn explicitly. The minimum
--   inequality is verified by bounding each minimum by capacity
--   and demand, using nonnegative convex weights and the weights
--   summing to one. It then multiplies the result by f(1)>=0.
--   The theorem does not assume integer demands or y>=0.
--
--   The original theorem1_conditional_concavity_base is Disproved
--   because it failed to assume f(1)>=0. This is the corrected
--   conditional base, not a proof of the full general Theorem 1
--   (which has to derive any needed positivity from condition (20)).
--   Only Prove2Me remote compilation is authoritative.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem NestedSeatAlloc.IntPolicy.condRevenue_one_concave_nonneg_fare {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ)
    (hM : IsSeatModel P X f) (hf1 : 0 ≤ f 1) (y : ℝ) :
    ConcaveOn ℝ (Set.Ici 0)
      (condRevenue P X f p 1 y) := by sorry
