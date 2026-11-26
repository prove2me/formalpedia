-- Prove2me | Theorems.Thm_FourierJacobi_Measure_unitConditionalMass_unitCenteredTail
-- name    : FourierJacobi.Measure.unitConditionalMass_unitCenteredTail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:43:55.156439+00:00
-- url     : https://prove2.me/theorems/b5419e74-c6ce-5d1b-b164-177485a12a96
-- title:
--   Measure: unit Conditional Mass unit Centered Tail
-- statement:
--   The Measure construction uses the unit Conditional Mass unit Centered Tail property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/LocalHaar.lean#L323-L334
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/LocalHaar.lean#L323-L334

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

theorem FourierJacobi.Measure.unitConditionalMass_unitCenteredTail (a : 𝒪[K]ˣ) (n : ℕ) :
    unitConditionalMass K (unitCenteredTail K a (n + 1)) =
      (residueCardinality K : ℝ)⁻¹ ^ n / (residueCardinality K - 1) := by sorry
