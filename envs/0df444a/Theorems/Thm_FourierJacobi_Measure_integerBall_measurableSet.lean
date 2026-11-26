-- Prove2me | Theorems.Thm_FourierJacobi_Measure_integerBall_measurableSet
-- name    : FourierJacobi.Measure.integerBall_measurableSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:41:40.224874+00:00
-- url     : https://prove2.me/theorems/a39c7122-e983-5b31-b999-fd66041d25fd
-- title:
--   Measure: integer Ball measurable Set
-- statement:
--   The Measure construction uses the integer Ball measurable Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/IntegerShells.lean#L201-L202
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/IntegerShells.lean#L201-L202

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

theorem FourierJacobi.Measure.integerBall_measurableSet (n : ℤ) : MeasurableSet (integerBall K n) := by sorry
