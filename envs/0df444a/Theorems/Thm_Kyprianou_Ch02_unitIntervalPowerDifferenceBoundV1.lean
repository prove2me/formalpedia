-- Prove2me | Theorems.Thm_Kyprianou_Ch02_unitIntervalPowerDifferenceBoundV1
-- name    : Kyprianou.Ch02.unitIntervalPowerDifferenceBoundV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T00:03:21.158683+00:00
-- url     : https://prove2.me/theorems/ef250556-4c96-48f3-8b0b-394e6f6c3525
-- title:
--   Powers on the unit interval are Lipschitz with constant the exponent
-- statement:
--   Apply the standard power difference estimate and bound the maximum absolute value by one.
-- source:
--   Kyprianou (2006), Exercise 2.8, independence of Jordan variation components.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.unitIntervalPowerDifferenceBoundV1
    (x y : ℝ) (hx : x ∈ Set.Icc 0 1) (hy : y ∈ Set.Icc 0 1) (N : ℕ) :
    |x^N-y^N| ≤ |x-y| * (N : ℝ) := by sorry
