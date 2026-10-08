-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_theorem1_global_optimality_base
-- name    : NestedSeatAlloc.IntPolicy.theorem1_global_optimality_base
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T07:28:28.338608+00:00
-- url     : https://prove2.me/theorems/7f9ccc1b-d251-4fe9-8aa4-a21d37b27b79
-- title:
--   Theorem 1 optimality base — one-class revenue is policy-dominated
-- statement:
--   At the first fare class, the selected policy's expected revenue dominates every protection policy at every nonnegative seat level.
-- source:
--   Source-faithful base case of Brumelle & McGill (1993), Theorem 1 global-optimality induction, pp. 131–132.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

namespace NestedSeatAlloc.IntPolicy

open MeasureTheory ProbabilityTheory

theorem theorem1_global_optimality_base {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ) (hM : IsSeatModel P X f)
    (hp : IsProtectionPolicy p) :
    ∀ q, IsProtectionPolicy q → ∀ s, 0 ≤ s →
      expRevenue P X f q 1 s ≤ expRevenue P X f p 1 s := by sorry

end NestedSeatAlloc.IntPolicy
