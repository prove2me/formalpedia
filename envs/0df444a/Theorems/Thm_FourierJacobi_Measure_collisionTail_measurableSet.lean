-- Prove2me | Theorems.Thm_FourierJacobi_Measure_collisionTail_measurableSet
-- name    : FourierJacobi.Measure.collisionTail_measurableSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:42:27.793881+00:00
-- url     : https://prove2.me/theorems/8b5ace73-4b8a-4b7e-93e5-6d96bf83dcb7
-- title:
--   Measure: collision Tail measurable Set
-- statement:
--   The Measure construction uses the collision Tail measurable Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/LocalHaar.lean#L189-L191
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/LocalHaar.lean#L189-L191

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

theorem FourierJacobi.Measure.collisionTail_measurableSet (n : ℕ) : MeasurableSet (collisionTail K n) := by sorry
