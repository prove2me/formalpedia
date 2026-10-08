-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_theorem1_fare_one_nonneg_of_min_increment_data
-- name    : NestedSeatAlloc.IntPolicy.theorem1_fare_one_nonneg_of_min_increment_data
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T21:08:58.157512+00:00
-- url     : https://prove2.me/theorems/646cb24e-a170-4d36-b058-d0b3bcff3283
-- title:
--   Theorem 1 base: condition (20) forces a nonnegative first fare
-- statement:
--   Assume the seat model, a nonnegative protection policy satisfying condition (20), and the exact level-one secant identity plus unit-interval expectation bounds for normalized min increments. Then the first fare is nonnegative. If it were negative, every positive right secant of level-one expected revenue would be at least f 1, forcing its right derivative to be at least f 1; condition (20) bounds that derivative by f 2, contradicting strict fare decrease.
-- source:
--   A source-faithful base-fare-sign reduction of theorem1_subdiff_condition_optimal (143e0912-6e16-4a92-9b63-63f65216560c), using its exact SubdiffCondition, IsSeatModel.fare_strictAnti, and level-one expRevenue definition. The hmean and hquot assumptions isolate the two independent analytic integral obligations so this child does not assume imported theorem statuses.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

open MeasureTheory ProbabilityTheory
open NestedSeatAlloc.IntPolicy

theorem NestedSeatAlloc.IntPolicy.theorem1_fare_one_nonneg_of_min_increment_data {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ) (hM : IsSeatModel P X f) (hp : IsProtectionPolicy p) (h20 : SubdiffCondition P X f p) (hmean : ∀ a h, 0 ≤ a → 0 < h → 0 ≤ ∫ ω, (min (a + h) (X 1 ω) - min a (X 1 ω)) / h ∂P ∧ (∫ ω, (min (a + h) (X 1 ω) - min a (X 1 ω)) / h ∂P) ≤ 1) (hquot : ∀ a h, 0 ≤ a → 0 < h → (expRevenue P X f p 1 (a + h) - expRevenue P X f p 1 a) / h = f 1 * ∫ ω, (min (a + h) (X 1 ω) - min a (X 1 ω)) / h ∂P) : 0 ≤ f 1 := by sorry
