-- Prove2me | Theorems.Thm_FourierJacobi_Measure_unitConditionalMass_collisionDepth_zero
-- name    : FourierJacobi.Measure.unitConditionalMass_collisionDepth_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:48:16.510413+00:00
-- url     : https://prove2.me/theorems/8ce5f9c4-df69-4d2f-aff1-97c11c45d83d
-- title:
--   Measure: unit Conditional Mass collision Depth zero
-- statement:
--   Cancellation mass at depth zero, inside the unit group.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/LocalHaar.lean#L289-L299
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/LocalHaar.lean#L289-L299

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

theorem FourierJacobi.Measure.unitConditionalMass_collisionDepth_zero :
    unitConditionalMass K (integralUnits K \ collisionTail K 1) =
      (residueCardinality K - 2) / (residueCardinality K - 1) := by sorry
