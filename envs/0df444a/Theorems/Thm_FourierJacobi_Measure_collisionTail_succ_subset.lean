-- Prove2me | Theorems.Thm_FourierJacobi_Measure_collisionTail_succ_subset
-- name    : FourierJacobi.Measure.collisionTail_succ_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:43:41.93526+00:00
-- url     : https://prove2.me/theorems/1ada28c1-25c9-5cb8-86a7-96c25fb84c21
-- title:
--   Measure: collision Tail succ subset
-- statement:
--   The Measure construction uses the collision Tail succ subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/LocalHaar.lean#L194-L196
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/LocalHaar.lean#L194-L196

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

theorem FourierJacobi.Measure.collisionTail_succ_subset (n : ℕ) :
    collisionTail K (n + 1) ⊆ collisionTail K n := by sorry
