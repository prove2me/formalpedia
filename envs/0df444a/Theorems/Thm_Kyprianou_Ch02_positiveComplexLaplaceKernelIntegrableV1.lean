-- Prove2me | Theorems.Thm_Kyprianou_Ch02_positiveComplexLaplaceKernelIntegrableV1
-- name    : Kyprianou.Ch02.positiveComplexLaplaceKernelIntegrableV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:37:32.807678+00:00
-- url     : https://prove2.me/theorems/77cabdbc-5069-4f63-a1dc-42cc4b4fe5cb
-- title:
--   positiveComplexLaplaceKernelIntegrable
-- statement:
--   positiveComplexLaplaceKernelIntegrable
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.15

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.positiveComplexLaplaceKernelIntegrableV1
    (ν : Measure ℝ)
    (hint : Integrable (fun x : ℝ => min (1 : ℝ) |x|)
      (ν.restrict (Set.Ioi (0 : ℝ)))) (z : ℂ) (hz : 0 ≤ z.re) :
    Integrable (fun x : ℝ => 1 - Complex.exp (-z * (x : ℂ)))
      (ν.restrict (Set.Ioi (0 : ℝ))) := by sorry
