-- Prove2me | Theorems.Thm_FourierJacobi_Measure_unitConditionalMass_collisionTail
-- name    : FourierJacobi.Measure.unitConditionalMass_collisionTail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:47:52.981148+00:00
-- url     : https://prove2.me/theorems/c082cd84-5de2-4528-84e7-6e3d4e0ee9d4
-- title:
--   Measure: unit Conditional Mass collision Tail
-- statement:
--   Cancellation tail law: depth at least n+1 has probability q^-n/(q-1).
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/LocalHaar.lean#L255-L262
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/LocalHaar.lean#L255-L262

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

theorem FourierJacobi.Measure.unitConditionalMass_collisionTail (n : ℕ) :
    unitConditionalMass K (collisionTail K (n + 1)) =
      (residueCardinality K : ℝ)⁻¹ ^ n / (residueCardinality K - 1) := by sorry
