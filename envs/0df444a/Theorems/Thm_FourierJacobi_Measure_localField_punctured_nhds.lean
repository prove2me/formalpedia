-- Prove2me | Theorems.Thm_FourierJacobi_Measure_localField_punctured_nhds
-- name    : FourierJacobi.Measure.localField_punctured_nhds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:18:41.523792+00:00
-- url     : https://prove2.me/theorems/37c33204-0050-4eec-a017-c392f5136e2d
-- title:
--   Measure: local Field punctured nhds
-- statement:
--   Every neighbourhood of zero in a nonarchimedean local field contains a
--   nonzero point. No residue characteristic or characteristic-zero restriction
--   is needed for this topological fact.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/NullSets.lean#L32-L45
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/NullSets.lean#L32-L45

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
  [IsNonarchimedeanLocalField K]

theorem FourierJacobi.Measure.localField_punctured_nhds : (𝓝[≠] (0 : K)).NeBot := by sorry
