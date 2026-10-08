-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_theorem2_integer_subdiff_policy_exists
-- name    : NestedSeatAlloc.IntPolicy.theorem2_integer_subdiff_policy_exists
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T22:27:57.081763+00:00
-- url     : https://prove2.me/theorems/a04f8201-2b54-4522-9148-3d975a84a09c
-- title:
--   Theorem 2 induction core — an integer protection policy satisfying (20) exists
-- statement:
--   Under the seat-model, integer-demand, and positive-fare hypotheses of Theorem 2, there exists an integer protection-level policy whose levels satisfy the subdifferential condition (20) at every nest. This is the induction-and-covering core of the theorem; the separate Theorem 1 implication turns such a policy into an optimal policy.
-- source:
--   Source-faithful decomposition of Brumelle–McGill (1993), Theorem 2, pp. 132–133; parent target 3e992204-8735-4d70-bcdb-3ba848cbcf0e at Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_NestedSeatAlloc_IntPolicy_CLBI

open MeasureTheory ProbabilityTheory

theorem NestedSeatAlloc.IntPolicy.theorem2_integer_subdiff_policy_exists {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f : ℕ → ℝ) (hM : NestedSeatAlloc.IntPolicy.IsSeatModel P X f)
    (hint : ∀ k ω, ∃ n : ℕ, X k ω = n) (hpos : ∀ k, 1 ≤ k → 0 < f k) :
    ∃ p : ℕ → ℕ, NestedSeatAlloc.IntPolicy.SubdiffCondition P X f (fun k => (p k : ℝ)) := by sorry
