-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_theorem2_expRevenue_prefix_policy_irrel
-- name    : NestedSeatAlloc.IntPolicy.theorem2_expRevenue_prefix_policy_irrel
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T11:59:16.599986+00:00
-- url     : https://prove2.me/theorems/48cd0208-5694-4e8f-b481-dd95dabe63d9
-- title:
--   Theorem 2 policy-prefix invariance — revenue through nest k ignores later policy entries
-- statement:
--   Expected revenue through nest k is unchanged when two policies agree on every protection level through k.
-- source:
--   Definitional consequence of the recursive revenue equations (8)–(9): the nest-k revenue reads only the protection prefix through k.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

namespace NestedSeatAlloc.IntPolicy

open MeasureTheory ProbabilityTheory

theorem theorem2_expRevenue_prefix_policy_irrel {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (f : ℕ → ℝ)
    (k : ℕ) (p q : ℕ → ℝ)
    (hpq : ∀ i, i ≤ k → p i = q i) :
    ∀ s, expRevenue P X f p k s = expRevenue P X f q k s := by sorry

end NestedSeatAlloc.IntPolicy
