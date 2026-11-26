-- Prove2me | Theorems.Thm_Kyprianou_Ch05_jumpPotentialKernelMeasurableV1
-- name    : Kyprianou.Ch05.jumpPotentialKernelMeasurableV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T16:06:16.991014+00:00
-- url     : https://prove2.me/theorems/f8aa9140-2385-57af-ae90-1fe2b3273587
-- title:
--   Joint passage kernel is a measurable integrated mark indicator
-- statement:
--   Express the mark integral as a section of a measurable indicator on the product; Tonelli measurability and indicator restriction give the exact kernel.
-- source:
--   Kyprianou (2006), Chapter 5, Theorem 5.6.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_LeanLevy_RandomMeasure_PoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory ProbabilityTheory Filter Set Complex Topology Kyprianou.Ch05
open scoped NNReal ENNReal Topology Classical
set_option autoImplicit false

theorem Kyprianou.Ch05.jumpPotentialKernelMeasurableV1
    (U Pi : Measure ℝ) [SigmaFinite Pi]
    (x : ℝ) (A B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    let f := (fun v : ℝ => if v ∈ Icc (0 : ℝ) x then
      ∫⁻ z in Ioi (x-v), if z-(x-v) ∈ A ∧ x-v ∈ B then (1 : ENNReal) else 0 ∂Pi
      else 0)
    Measurable f ∧ jumpPotentialKernel U Pi x A B = ∫⁻ v, f v ∂U := by
  sorry
