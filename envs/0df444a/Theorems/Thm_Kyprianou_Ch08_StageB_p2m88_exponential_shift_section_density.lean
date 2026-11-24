-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_exponential_shift_section_density
-- name    : Kyprianou.Ch08.StageB.p2m88_exponential_shift_section_density
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:10:50.527879+00:00
-- url     : https://prove2.me/theorems/fca55413-301c-4c3a-a4c1-feb4b8f1d04e
-- title:
--   Translated exponential law has a strict-positive Lebesgue density
-- statement:
--   The mass of a measurable set under translation by c of a positive-rate exponential law equals the integral of its translated exponential density over that set, supported on the strict upper ray. Removing the endpoint does not change Lebesgue mass.
-- source:
--   Kyprianou (2006), Theorem 8.7, convolution of the two independent Wiener–Hopf factors.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Measure.Prod
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB

/-- Translated exponential law has a strict-positive Lebesgue density -/
theorem p2m88_exponential_shift_section_density :
    ∀ (φ c : ℝ), 0 < φ → ∀ A : Set ℝ, MeasurableSet A →
      (expMeasure φ) ((fun s : ℝ => s + c) ⁻¹' A) =
        ∫⁻ y in A, (Ioi c).indicator
          (fun y => ENNReal.ofReal (φ * Real.exp (-φ * (y - c)))) y := by
  sorry

end Kyprianou.Ch08.StageB
