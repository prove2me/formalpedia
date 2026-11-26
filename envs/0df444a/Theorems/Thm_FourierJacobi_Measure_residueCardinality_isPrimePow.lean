-- Prove2me | Theorems.Thm_FourierJacobi_Measure_residueCardinality_isPrimePow
-- name    : FourierJacobi.Measure.residueCardinality_isPrimePow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:43:25.563973+00:00
-- url     : https://prove2.me/theorems/1e1ef3fd-10d9-4282-b003-dbefa3ab87ec
-- title:
--   Measure: residue Cardinality is Prime Pow
-- statement:
--   The Measure construction uses the residue Cardinality is Prime Pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/LocalHaar.lean#L62-L65
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/LocalHaar.lean#L62-L65

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

theorem FourierJacobi.Measure.residueCardinality_isPrimePow : IsPrimePow (residueCardinality K) := by sorry
