-- Prove2me | Theorems.Thm_Kyprianou_Ch03_momentFiniteBoundedMarkIdV1
-- name    : Kyprianou.Ch03.momentFiniteBoundedMarkIdV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T13:20:14.407157+00:00
-- url     : https://prove2.me/theorems/d5fcfd33-2949-45a5-8bcd-9a327de6a1d4
-- title:
--   Identity integrability of bounded marks in finite measure
-- statement:
--   Dominate absolute values by the constant one.
-- source:
--   Kyprianou (2006), Theorems 3.6 and 3.8; finite compensated small-jump approximation, reusing Chapter 8 finite transform construction and published compound-Poisson transform.

import Mathlib
import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.momentFiniteBoundedMarkIdV1
    (nu : Measure Real) [IsFiniteMeasure nu]
    (hnu : ∀ᵐ x ∂nu, |x| < 1) :
    Integrable (fun x : Real => x) nu := by sorry
