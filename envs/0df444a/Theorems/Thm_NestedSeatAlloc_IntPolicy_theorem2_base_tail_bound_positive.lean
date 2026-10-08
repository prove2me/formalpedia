-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_theorem2_base_tail_bound_positive
-- name    : NestedSeatAlloc.IntPolicy.theorem2_base_tail_bound_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T10:36:06.496121+00:00
-- url     : https://prove2.me/theorems/93c61177-e94e-4e43-b275-6f5a3e536ab3
-- title:
--   Theorem 2 strict base tail bound — a positive seat level falls below the next fare
-- statement:
--   For the one-class expected revenue with integer-valued demand and positive fares, there is a strictly positive seat level whose right derivative is below the second fare.
-- source:
--   Source-faithful strict form of the one-class tail-limit bridge used with the CLBI covering argument in Brumelle & McGill (1993), Theorem 2, pp. 132–133.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_NestedSeatAlloc_IntPolicy_CLBI

namespace NestedSeatAlloc.IntPolicy

open MeasureTheory ProbabilityTheory

theorem theorem2_base_tail_bound_positive {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ)
    (hM : IsSeatModel P X f)
    (hint : ∀ k ω, ∃ n : ℕ, X k ω = n)
    (hpos : ∀ k, 1 ≤ k → 0 < f k) :
    ∃ s, 0 < s ∧ ∃ r,
      HasDerivWithinAt (expRevenue P X f p 1) r (Set.Ici s) s ∧ r < f 2 := by sorry

end NestedSeatAlloc.IntPolicy
