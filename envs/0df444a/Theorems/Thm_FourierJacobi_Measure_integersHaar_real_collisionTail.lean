-- Prove2me | Theorems.Thm_FourierJacobi_Measure_integersHaar_real_collisionTail
-- name    : FourierJacobi.Measure.integersHaar_real_collisionTail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:41:14.148603+00:00
-- url     : https://prove2.me/theorems/0dd6586c-779f-546d-b97a-44f2ef98542f
-- title:
--   Measure: integers Haar real collision Tail
-- statement:
--   The Measure construction uses the integers Haar real collision Tail property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/LocalHaar.lean#L232-L234
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/LocalHaar.lean#L232-L234

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

theorem FourierJacobi.Measure.integersHaar_real_collisionTail (n : ℕ) :
    (integersHaar K).real (collisionTail K n) = (residueCardinality K : ℝ)⁻¹ ^ n := by sorry
