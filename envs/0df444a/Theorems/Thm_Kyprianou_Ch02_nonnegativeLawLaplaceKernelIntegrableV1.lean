-- Prove2me | Theorems.Thm_Kyprianou_Ch02_nonnegativeLawLaplaceKernelIntegrableV1
-- name    : Kyprianou.Ch02.nonnegativeLawLaplaceKernelIntegrableV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:58:41.441411+00:00
-- url     : https://prove2.me/theorems/01d4e2a3-eb83-4c2b-8037-249be36a6b1a
-- title:
--   nonnegativeLawLaplaceKernelIntegrable
-- statement:
--   nonnegativeLawLaplaceKernelIntegrable
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.15

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.nonnegativeLawLaplaceKernelIntegrableV1
    (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (hQ : Q (Set.Iio (0 : ℝ)) = 0) (z : ℂ) (hz : 0 ≤ z.re) :
    Integrable (fun x : ℝ => Complex.exp (-z * (x : ℂ))) Q := by sorry
