-- Prove2me | Theorems.Thm_Kyprianou_Ch04_simpleMarkIntensityFibresV1
-- name    : Kyprianou.Ch04.simpleMarkIntensityFibresV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:37:26.665804+00:00
-- url     : https://prove2.me/theorems/c0cf0268-d981-5bc6-9be3-a4ad56dde46c
-- title:
--   Signed simple mark intensity integral as fibre sum
-- statement:
--   A simple mark integral over a finite measure region is the weighted sum of the measures of its fibres.
-- source:
--   Kyprianou (2006), Exercise 4.5(ii); finite marked Poisson moment calculation.

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem simpleMarkIntensityFibresV1 (ν : Measure ℝ) (B : Set ℝ) (hB : MeasurableSet B)
    (hfinite : ν B < ⊤) (g : SimpleFunc ℝ ℝ) :
    (∫ x in B, g x ∂ν) = ∑ r ∈ g.range, r * (ν (B ∩ g ⁻¹' {r})).toReal := by
  sorry
end Kyprianou.Ch04
