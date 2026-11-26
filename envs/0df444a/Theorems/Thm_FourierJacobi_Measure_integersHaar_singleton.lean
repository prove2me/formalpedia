-- Prove2me | Theorems.Thm_FourierJacobi_Measure_integersHaar_singleton
-- name    : FourierJacobi.Measure.integersHaar_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:43:58.204278+00:00
-- url     : https://prove2.me/theorems/0e03acf8-09c4-5c50-af37-86ce8b698033
-- title:
--   Measure: integers Haar singleton
-- statement:
--   In particular every point of the valuation ring has zero pulled-back Haar mass.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/LocalHaar.lean#L382-L384
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/LocalHaar.lean#L382-L384

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

theorem FourierJacobi.Measure.integersHaar_singleton (x : 𝒪[K]) : integersHaar K {x} = 0 := by sorry
