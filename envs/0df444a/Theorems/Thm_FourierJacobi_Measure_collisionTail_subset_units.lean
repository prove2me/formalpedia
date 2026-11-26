-- Prove2me | Theorems.Thm_FourierJacobi_Measure_collisionTail_subset_units
-- name    : FourierJacobi.Measure.collisionTail_subset_units
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:41:19.83093+00:00
-- url     : https://prove2.me/theorems/26bc6d37-73fb-4ec1-bbb7-a7386d0b49d7
-- title:
--   Measure: collision Tail subset units
-- statement:
--   The Measure construction uses the collision Tail subset units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/LocalHaar.lean#L199-L208
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/LocalHaar.lean#L199-L208

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

theorem FourierJacobi.Measure.collisionTail_subset_units {n : ℕ} (hn : 0 < n) :
    collisionTail K n ⊆ integralUnits K := by sorry
