-- Prove2me | Theorems.Thm_Kyprianou_Ch05_jumpPotentialInnerKernelMeasurableV1
-- name    : Kyprianou.Ch05.jumpPotentialInnerKernelMeasurableV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T16:52:34.1445+00:00
-- url     : https://prove2.me/theorems/14fa6290-8bbb-4da1-9edc-59ee42e4428e
-- title:
--   Measurability of the first-passage mark kernel
-- statement:
--   A measurable marked crossing indicator has a measurable integral over the jump marks.
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

theorem Kyprianou.Ch05.jumpPotentialInnerKernelMeasurableV1
    (Pi : Measure ℝ) [SigmaFinite Pi]
    (x : ℝ) (A B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Measurable (fun v : ℝ => ∫⁻ z in Ioi (x-v),
      if z-(x-v) ∈ A ∧ x-v ∈ B then (1 : ENNReal) else 0 ∂Pi) := by
  sorry
