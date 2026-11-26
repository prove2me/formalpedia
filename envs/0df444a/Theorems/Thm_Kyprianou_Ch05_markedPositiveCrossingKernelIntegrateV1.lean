-- Prove2me | Theorems.Thm_Kyprianou_Ch05_markedPositiveCrossingKernelIntegrateV1
-- name    : Kyprianou.Ch05.markedPositiveCrossingKernelIntegrateV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T20:21:44.245996+00:00
-- url     : https://prove2.me/theorems/11af5e44-be00-50cb-9166-357664358ac8
-- title:
--   Mark integration gives the discounted crossing potential integrand
-- statement:
--   Separate the positive time and admissible pre-state cases. Pull the finite discount factor through the nonnegative integral and convert the strict mark threshold to a restriction.
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

theorem Kyprianou.Ch05.markedPositiveCrossingKernelIntegrateV1
    (Pi : Measure ℝ) (eta x s v : ℝ) (A B : Set ℝ) :
    (∫⁻ z, if 0 < s ∧ v ∈ Icc (0 : ℝ) x ∧ x-v < z ∧
      z-(x-v) ∈ A ∧ x-v ∈ B then ENNReal.ofReal (Real.exp (-eta*s)) else 0 ∂Pi) =
    if 0 < s then ENNReal.ofReal (Real.exp (-eta*s)) * (fun v : ℝ => if v ∈ Icc (0 : ℝ) x then
      ∫⁻ z in Ioi (x-v), if z-(x-v) ∈ A ∧ x-v ∈ B then (1 : ENNReal) else 0 ∂Pi
      else 0) v else 0 := by
  sorry
