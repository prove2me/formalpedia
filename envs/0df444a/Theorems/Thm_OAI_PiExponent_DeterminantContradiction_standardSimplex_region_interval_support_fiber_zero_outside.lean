-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standardSimplex_region_interval_support_fiber_zero_outside
-- name    : OAI.PiExponent.DeterminantContradiction.standardSimplex_region_interval_support.fiber_zero_outside
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T15:35:14.292467+00:00
-- url     : https://prove2.me/theorems/a7499cae-8dd9-4599-b7cd-72692830cd21
-- title:
--   The constrained simplex fiber is empty outside its parameter range
-- statement:
--   For any dimension, the constrained fiber has zero volume if its parameter is negative or exceeds `H`: in the latter case its coordinate sum would have to be both nonnegative and strictly negative.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.standardSimplex_region_interval_support.fiber_zero_outside (m : Nat) (H t : Real) (ht : t < 0 ∨ H < t) :
    (MeasureTheory.volume {x : Fin m → Real | 0 ≤ t ∧ (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ H - t}).toReal = 0 := by sorry
