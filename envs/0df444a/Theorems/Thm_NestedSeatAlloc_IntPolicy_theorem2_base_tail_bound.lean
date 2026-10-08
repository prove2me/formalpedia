-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_theorem2_base_tail_bound
-- name    : NestedSeatAlloc.IntPolicy.theorem2_base_tail_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T08:14:50.346075+00:00
-- url     : https://prove2.me/theorems/892a3017-35ef-42b9-b5f5-69f453d8b1a7
-- title:
--   Theorem 2 base tail bound — Eq. (27) eventually falls below the next fare
-- statement:
--   For the one-class expected revenue with integer-valued demand and positive fares, some nonnegative seat level has a right derivative strictly below the second fare.
-- source:
--   Source-faithful tail-limit bridge for the base case of Brumelle & McGill (1993), Theorem 2, using Eq. (27) and positivity of f₂, pp. 132–133.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_NestedSeatAlloc_IntPolicy_CLBI

namespace NestedSeatAlloc.IntPolicy

open MeasureTheory ProbabilityTheory

theorem theorem2_base_tail_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ)
    (hM : IsSeatModel P X f)
    (hint : ∀ k ω, ∃ n : ℕ, X k ω = n)
    (hpos : ∀ k, 1 ≤ k → 0 < f k) :
    ∃ s, 0 ≤ s ∧ ∃ r,
      HasDerivWithinAt (expRevenue P X f p 1) r (Set.Ici s) s ∧ r < f 2 := by sorry

end NestedSeatAlloc.IntPolicy
