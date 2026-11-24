-- Prove2me | Theorems.Thm_Kyprianou_Ch03_momentFiniteBoundedMarkExpV1
-- name    : Kyprianou.Ch03.momentFiniteBoundedMarkExpV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T13:20:17.183066+00:00
-- url     : https://prove2.me/theorems/e046ff44-98ad-4a71-93eb-57f3beac4fbf
-- title:
--   Exponential integrability of bounded marks in finite measure
-- statement:
--   Dominate by exp(|b|) on the unit interval.
-- source:
--   Kyprianou (2006), Theorems 3.6 and 3.8; finite compensated small-jump approximation, reusing Chapter 8 finite transform construction and published compound-Poisson transform.

import Mathlib
import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.momentFiniteBoundedMarkExpV1
    (nu : Measure Real) [IsFiniteMeasure nu]
    (hnu : ∀ᵐ x ∂nu, |x| < 1) (b : Real) :
    Integrable (fun x : Real => Real.exp (b * x)) nu := by sorry
