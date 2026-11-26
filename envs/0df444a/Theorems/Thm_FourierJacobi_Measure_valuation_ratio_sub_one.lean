-- Prove2me | Theorems.Thm_FourierJacobi_Measure_valuation_ratio_sub_one
-- name    : FourierJacobi.Measure.valuation_ratio_sub_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:43:57.774683+00:00
-- url     : https://prove2.me/theorems/e362be7f-630b-5e02-ac1d-8886575f5821
-- title:
--   Measure: valuation ratio sub one
-- statement:
--   For an integral unit denominator, the ratio's cancellation depth is the depth
--   of the difference. This is the key elementary step for a fixed unit numerator.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/LocalHaar.lean#L340-L350
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/LocalHaar.lean#L340-L350

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
omit [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [MeasurableSpace K] [BorelSpace K]

theorem FourierJacobi.Measure.valuation_ratio_sub_one (a x : 𝒪[K]) (hx : IsUnit x) :
    valuation K ((a : K) / (x : K) - 1) = valuation K ((x : K) - (a : K)) := by sorry
