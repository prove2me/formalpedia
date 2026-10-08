-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_conditionalRevenue_succ_piecewise
-- name    : NestedSeatAlloc.IntPolicy.conditionalRevenue_succ_piecewise
-- status  : Open
-- author  : @WillR
-- created : 2026-10-06T20:53:14.070975+00:00
-- url     : https://prove2.me/theorems/bb63bdf0-f1c3-41b0-ad50-c2a266c02316
-- title:
--   Conditional revenue one-step three-region decomposition
-- statement:
--   Conditional revenue at level k+1 decomposes into the previous conditional revenue below p k, an affine middle branch of slope f (k+1), and a translated previous conditional revenue above p k plus y.
-- source:
--   Source-faithful three-region conditional-revenue recursion used in Brumelle & McGill (1993), Theorem 1 concavity induction. This child isolates the missing model decomposition needed before the parent can split its concavity proof across the three regions.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

namespace NestedSeatAlloc.IntPolicy

open MeasureTheory ProbabilityTheory

theorem conditionalRevenue_succ_piecewise
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ)
    (k : ℕ) (y s : ℝ)
    (hM : IsSeatModel P X f) (hp : IsProtectionPolicy p)
    (hy : 0 ≤ y) :
    condRevenue P X f p (k + 1) y s =
      (if s < p k then condRevenue P X f p k y s
       else if s < p k + y then
         (s - p k) * f (k + 1) + condRevenue P X f p k y (p k)
       else y * f (k + 1) + condRevenue P X f p k y (s - y)) := by sorry

end NestedSeatAlloc.IntPolicy
