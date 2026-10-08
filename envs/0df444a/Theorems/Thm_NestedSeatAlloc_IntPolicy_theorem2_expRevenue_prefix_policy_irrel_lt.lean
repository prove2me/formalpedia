-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_theorem2_expRevenue_prefix_policy_irrel_lt
-- name    : NestedSeatAlloc.IntPolicy.theorem2_expRevenue_prefix_policy_irrel_lt
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T11:59:36.932672+00:00
-- url     : https://prove2.me/theorems/72ab1213-9d2f-4fee-8117-480492659979
-- title:
--   Theorem 2 strict prefix invariance — ER_k ignores policy entries at and beyond k
-- statement:
--   Expected revenue through nest k is unchanged when two policies agree at every index strictly below k.
-- source:
--   Definitional consequence of the recursive revenue equations (8)–(9): ER_k reads protection levels only below k.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

namespace NestedSeatAlloc.IntPolicy

open MeasureTheory ProbabilityTheory

theorem theorem2_expRevenue_prefix_policy_irrel_lt {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (f : ℕ → ℝ)
    (k : ℕ) (p q : ℕ → ℝ)
    (hpq : ∀ i, i < k → p i = q i) :
    ∀ s, expRevenue P X f p k s = expRevenue P X f q k s := by sorry

end NestedSeatAlloc.IntPolicy
