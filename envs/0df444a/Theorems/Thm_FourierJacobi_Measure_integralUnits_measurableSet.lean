-- Prove2me | Theorems.Thm_FourierJacobi_Measure_integralUnits_measurableSet
-- name    : FourierJacobi.Measure.integralUnits_measurableSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:45:23.535257+00:00
-- url     : https://prove2.me/theorems/0aac339f-f413-4331-a824-517b98df482e
-- title:
--   Measure: integral Units measurable Set
-- statement:
--   The Measure construction uses the integral Units measurable Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/LocalHaar.lean#L159-L160
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/LocalHaar.lean#L159-L160

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

theorem FourierJacobi.Measure.integralUnits_measurableSet : MeasurableSet (integralUnits K) := by sorry
