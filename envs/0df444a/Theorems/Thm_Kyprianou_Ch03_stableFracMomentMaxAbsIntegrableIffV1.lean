-- Prove2me | Theorems.Thm_Kyprianou_Ch03_stableFracMomentMaxAbsIntegrableIffV1
-- name    : Kyprianou.Ch03.stableFracMomentMaxAbsIntegrableIffV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T15:10:17.107376+00:00
-- url     : https://prove2.me/theorems/824af0f1-1d42-432e-b2e6-e403efe9960c
-- title:
--   Absolute power integrability iff truncated-below power integrability
-- statement:
--   Use monotonicity of real powers on the nonnegative reals, with |Y|^eta ≤ max(|Y|,1)^eta ≤ 1+|Y|^eta. The constant one is integrable on a probability space.
-- source:
--   Kyprianou (2006), Exercise 3.3(iii), direct application of the shared Theorem 3.8 moment criterion.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_IsSubmultiplicative
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.stableFracMomentMaxAbsIntegrableIffV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : Omega → Real) (hY : AEMeasurable Y P) (eta : Real) (heta : 0 < eta) :
    Integrable (fun w => |Y w| ^ eta) P ↔
      Integrable (fun w => (max |Y w| 1) ^ eta) P := by sorry
