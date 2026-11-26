-- Prove2me | Theorems.Thm_FourierJacobi_Measure_localField_coordinates_determinant_ae
-- name    : FourierJacobi.Measure.localField_coordinates_determinant_ae
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:59:35.747257+00:00
-- url     : https://prove2.me/theorems/196df854-fab3-49ff-bbb3-22a59e739c3a
-- title:
--   Measure: local Field coordinates determinant ae
-- statement:
--   The exceptional sets in expanded:null are null for additive Haar on
--   every nonarchimedean local field, including every field in Theorem 2.2.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/NullSets.lean#L149-L163
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/NullSets.lean#L149-L163

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

theorem FourierJacobi.Measure.localField_coordinates_determinant_ae (z : K) :
    ∀ᵐ p : K × K ∂μ.prod μ,
      p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ p.2 ^ 2 - p.1 * z ≠ 0 := by sorry
