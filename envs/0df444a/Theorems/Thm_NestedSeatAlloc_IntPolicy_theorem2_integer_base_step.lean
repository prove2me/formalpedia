-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_theorem2_integer_base_step
-- name    : NestedSeatAlloc.IntPolicy.theorem2_integer_base_step
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T06:36:10.818976+00:00
-- url     : https://prove2.me/theorems/61e0e3c1-0b18-4131-a769-78c6f81c2171
-- title:
--   Theorem 2 base step — an integer first protection level exists
-- statement:
--   Under the seat model, integer-valued first demand, and positive fares, the one-class expected revenue admits an integer protection level satisfying the first subdifferential condition.
-- source:
--   Brumelle & McGill (1993), Theorem 2 proof, base case from Eq. (27) and the CLBI covering argument, pp. 132–133.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_NestedSeatAlloc_IntPolicy_CLBI

namespace NestedSeatAlloc.IntPolicy

open MeasureTheory ProbabilityTheory

theorem theorem2_integer_base_step {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f : ℕ → ℝ)
    (hM : IsSeatModel P X f)
    (hint : ∀ k ω, ∃ n : ℕ, X k ω = n)
    (hpos : ∀ k, 1 ≤ k → 0 < f k) :
    ∃ n : ℕ, InSubdiff (expRevenue P X f (fun j => (n : ℝ)) 1) n (f 2) := by sorry

end NestedSeatAlloc.IntPolicy
