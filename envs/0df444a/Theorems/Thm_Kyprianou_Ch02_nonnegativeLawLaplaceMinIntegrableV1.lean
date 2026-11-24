-- Prove2me | Theorems.Thm_Kyprianou_Ch02_nonnegativeLawLaplaceMinIntegrableV1
-- name    : Kyprianou.Ch02.nonnegativeLawLaplaceMinIntegrableV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:58:55.776084+00:00
-- url     : https://prove2.me/theorems/11a4217a-616e-47c1-8ace-f0f5f483ddff
-- title:
--   nonnegativeLawLaplaceMinIntegrable
-- statement:
--   nonnegativeLawLaplaceMinIntegrable
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.15

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.nonnegativeLawLaplaceMinIntegrableV1
    (Q : Measure ℝ) [IsProbabilityMeasure Q] :
    Integrable (fun x : ℝ => min (1 : ℝ) |x|) Q := by sorry
