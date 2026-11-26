-- Prove2me | Theorems.Thm_FourierJacobi_Measure_integerShell_measurableSet
-- name    : FourierJacobi.Measure.integerShell_measurableSet
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:41:37.740951+00:00
-- url     : https://prove2.me/theorems/e29f8b1d-f23a-56ce-909a-3b0c069957b5
-- title:
--   Measure: integer Shell measurable Set
-- statement:
--   The Measure construction uses the integer Shell measurable Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/IntegerShells.lean#L204-L206
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/IntegerShells.lean#L204-L206

import Definitions.Def_FourierJacobi_Measure_LocalHaar
import Definitions.Def_FourierJacobi_Valuations_LocalField
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Definitions.Def_FourierJacobi_Measure_IntegerShells
set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel FourierJacobi.Valuations
open scoped ENNReal NNReal Pointwise WithZero
open FourierJacobi FourierJacobi.Measure
set_option maxHeartbeats 2000000
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
attribute [local instance] FourierJacobi.Measure.integerShells_t2Space
variable [MeasurableSpace K] [BorelSpace K]
attribute [local instance] FourierJacobi.Measure.integerShells_additiveHaar_regular

theorem FourierJacobi.Measure.integerShell_measurableSet (n : ℤ) : MeasurableSet (integerShell K n) := by sorry
