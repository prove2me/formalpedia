-- Prove2me | Theorems.Thm_FourierJacobi_Measure_localField_haar_nullSingletonClass
-- name    : FourierJacobi.Measure.localField_haar_nullSingletonClass
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T10:49:23.053651+00:00
-- url     : https://prove2.me/theorems/b562bb29-4f95-5784-811c-7cb4f26a2ae3
-- title:
--   Measure: local Field haar null Singleton Class
-- statement:
--   Atomlessness is proved from the general local-field and Haar hypotheses,
--   not added as an assumption of the local-field application.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/NullSets.lean#L141-L145
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/NullSets.lean#L141-L145

import Mathlib.NumberTheory.LocalField.Basic
import Definitions.Def_FourierJacobi_Valuations_LocalField
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FunProp
import Definitions.Def_FourierJacobi_Measure_NullSets
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open FourierJacobi FourierJacobi.Measure
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K]
  (μ : MeasureTheory.Measure K) [μ.IsAddHaarMeasure]

theorem FourierJacobi.Measure.localField_haar_nullSingletonClass : NullSingletonClass μ := by sorry
