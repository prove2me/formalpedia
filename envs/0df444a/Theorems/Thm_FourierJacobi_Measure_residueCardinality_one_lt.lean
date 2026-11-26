-- Prove2me | Theorems.Thm_FourierJacobi_Measure_residueCardinality_one_lt
-- name    : FourierJacobi.Measure.residueCardinality_one_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:41:07.337552+00:00
-- url     : https://prove2.me/theorems/fcd0de8e-7b17-5739-b73e-83445649afdd
-- title:
--   Measure: residue Cardinality one lt
-- statement:
--   The Measure construction uses the residue Cardinality one lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/LocalHaar.lean#L68-L70
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/LocalHaar.lean#L68-L70

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
omit [MeasurableSpace K] [BorelSpace K]

theorem FourierJacobi.Measure.residueCardinality_one_lt : 1 < residueCardinality K := by sorry
