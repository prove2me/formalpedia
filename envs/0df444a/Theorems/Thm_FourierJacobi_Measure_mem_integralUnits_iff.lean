-- Prove2me | Theorems.Thm_FourierJacobi_Measure_mem_integralUnits_iff
-- name    : FourierJacobi.Measure.mem_integralUnits_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:41:57.792508+00:00
-- url     : https://prove2.me/theorems/52465e5d-fee7-5101-9c18-6facf2443138
-- title:
--   Measure: mem integral Units iff
-- statement:
--   The Measure construction uses the mem integral Units iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/LocalHaar.lean#L156-L157
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/LocalHaar.lean#L156-L157

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

theorem FourierJacobi.Measure.mem_integralUnits_iff (x : 𝒪[K]) : x ∈ integralUnits K ↔ IsUnit x := by sorry
