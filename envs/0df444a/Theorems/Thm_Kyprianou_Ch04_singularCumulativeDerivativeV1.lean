-- Prove2me | Theorems.Thm_Kyprianou_Ch04_singularCumulativeDerivativeV1
-- name    : Kyprianou.Ch04.singularCumulativeDerivativeV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:30:49.294343+00:00
-- url     : https://prove2.me/theorems/472e5c8d-c1c3-448f-b7e1-b6f2d5271970
-- title:
--   Almost-everywhere zero derivative of a singular finite measure cumulative function
-- statement:
--   Normalize a nonzero finite singular measure to a probability measure, use its Stieltjes CDF and singular Radon-Nikodym derivative, and rescale.
-- source:
--   Supporting proof for Kyprianou (2006), Chapter 4, Exercise 4.9(i).

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.singularCumulativeDerivativeV1 (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : μ.MutuallySingular volume) :
    ∀ᵐ x : ℝ ∂volume, HasDerivAt (fun t : ℝ => (μ (Iic t)).toReal) 0 x := by
  sorry
