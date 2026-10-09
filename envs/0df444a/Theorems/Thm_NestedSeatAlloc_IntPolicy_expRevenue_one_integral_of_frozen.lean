-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_expRevenue_one_integral_of_frozen
-- name    : NestedSeatAlloc.IntPolicy.expRevenue_one_integral_of_frozen
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T16:07:09.986965+00:00
-- url     : https://prove2.me/theorems/aceff346-eb9b-469f-b7e9-1641bfe878bb
-- title:
--   Class-one expected revenue is the expectation of frozen first-class conditional revenue
-- statement:
--   Expected revenue at class one equals the expectation, over the
--   actual first-class demand X(1), of the first-class revenue evaluated
--   at that frozen demand. This follows by pointwise identity from the
--   Proved condRevenue_one_frozen_formula, without any independence,
--   disintegration, interchange of integrals or new sign assumptions.
--   The equality permits applying the already Proved generic theorem
--   concaveOn_of_ae_integral_representation to obtain concavity of the
--   first-class expected revenue, provided non-negative fare is known
--   and integrability is justified. No local Lean or Lake compilation.
-- source:
--   Expected revenue at class one equals the expectation, over the
--   actual first-class demand X(1), of the first-class revenue evaluated
--   at that frozen demand. This follows by pointwise identity from the
--   Proved condRevenue_one_frozen_formula, without any independence,
--   disintegration, interchange of integrals or new sign assumptions.
--   The equality permits applying the already Proved generic theorem
--   concaveOn_of_ae_integral_representation to obtain concavity of the
--   first-class expected revenue, provided non-negative fare is known
--   and integrability is justified. No local Lean or Lake compilation.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem NestedSeatAlloc.IntPolicy.expRevenue_one_integral_of_frozen {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ)
    (hM : IsSeatModel P X f) (s : ℝ) :
    expRevenue P X f p 1 s =
      ∫ ω, condRevenue P X f p 1 (X 1 ω) s ∂P := by sorry
