-- Prove2me | Theorems.Thm_FourierJacobi_Measure_unitConditionalMass_of_subset
-- name    : FourierJacobi.Measure.unitConditionalMass_of_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:41:14.87884+00:00
-- url     : https://prove2.me/theorems/d4485af7-aeb8-5d1d-aad2-0ddae2333813
-- title:
--   Measure: unit Conditional Mass of subset
-- statement:
--   The Measure construction uses the unit Conditional Mass of subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/LocalHaar.lean#L248-L252
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/LocalHaar.lean#L248-L252

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

theorem FourierJacobi.Measure.unitConditionalMass_of_subset (s : Set 𝒪[K]) (hs : s ⊆ integralUnits K) :
    unitConditionalMass K s = (integersHaar K).real s /
      (1 - (residueCardinality K : ℝ)⁻¹) := by sorry
