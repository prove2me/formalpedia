-- Prove2me | Theorems.Thm_FourierJacobi_Measure_integersHaar_integralUnits
-- name    : FourierJacobi.Measure.integersHaar_integralUnits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:45:35.228806+00:00
-- url     : https://prove2.me/theorems/aa395a16-0352-4e24-a5c5-d6ed4669db96
-- title:
--   Measure: integers Haar integral Units
-- statement:
--   Additive volume of the units, with precisely the manuscript's normalization.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/LocalHaar.lean#L163-L167
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/LocalHaar.lean#L163-L167

import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.MeasureTheory.Measure.Real
import Definitions.Def_FourierJacobi_Measure_NullSets
import Definitions.Def_FourierJacobi_Measure_LocalHaar
set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel
open scoped ENNReal NNReal
open FourierJacobi FourierJacobi.Measure
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
attribute [local instance] FourierJacobi.Measure.localField_t2Space
variable [MeasurableSpace K] [BorelSpace K]

theorem FourierJacobi.Measure.integersHaar_integralUnits :
    integersHaar K (integralUnits K) = 1 - (residueCardinality K : ℝ≥0∞)⁻¹ := by sorry
