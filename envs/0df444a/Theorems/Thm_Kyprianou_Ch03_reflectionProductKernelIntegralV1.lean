-- Prove2me | Theorems.Thm_Kyprianou_Ch03_reflectionProductKernelIntegralV1
-- name    : Kyprianou.Ch03.reflectionProductKernelIntegralV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T21:47:48.483494+00:00
-- url     : https://prove2.me/theorems/7900b9a7-4f6b-47c2-9d68-993da8e4b303
-- title:
--   Integrate bounded kernels against a joint product law
-- statement:
--   Replace the stopped state by a measurable version, use map integration and Fubini for the product law.
-- source:
--   Kyprianou (2006), Exercise 3.2, stopped-state kernel proof.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_LevyExtrema_SBA_runSup
import Definitions.Def_Kyprianou_Ch03_ReflectedProcesses
open MeasureTheory ProbabilityTheory Filter Kyprianou.Ch03
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch03.reflectionProductKernelIntegralV1
    {Omega : Type} [MeasurableSpace Omega]
    (mu P : Measure Omega) [IsFiniteMeasure mu] [IsProbabilityMeasure P]
    (S : Omega → ℝ) (Y Z : Omega → (NNReal → ℝ))
    (hS : AEMeasurable S mu) (hY : AEMeasurable Y mu) (hZ : Measurable Z)
    (hLaw : Measure.map (fun w => (S w,Y w)) mu =
      (Measure.map S mu).prod (Measure.map Z P))
    (H : ℝ × (NNReal → ℝ) → ℝ) (hH : Measurable H)
    (hBound : ∃ C : ℝ, 0 ≤ C ∧ ∀ z, |H z| ≤ C) :
    (∫ w, H (S w,Y w) ∂mu) = ∫ w, (∫ eta, H (S w,Z eta) ∂P) ∂mu := by sorry
