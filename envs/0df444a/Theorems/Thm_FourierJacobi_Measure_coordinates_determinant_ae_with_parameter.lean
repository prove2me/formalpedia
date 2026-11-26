-- Prove2me | Theorems.Thm_FourierJacobi_Measure_coordinates_determinant_ae_with_parameter
-- name    : FourierJacobi.Measure.coordinates_determinant_ae_with_parameter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:18:54.386825+00:00
-- url     : https://prove2.me/theorems/71a718bf-c308-4ab5-90db-ea0682c7cae8
-- title:
--   Measure: coordinates determinant ae with parameter
-- statement:
--   Extra, possibly unbounded coordinates do not spoil null-set removal.
--   No finiteness hypothesis on their measure is required.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/NullSets.lean#L118-L130
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/NullSets.lean#L118-L130

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
variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [SecondCountableTopology K]
  [T2Space K] [MeasurableSpace K] [BorelSpace K]
  (μ ν : MeasureTheory.Measure K) [NullSingletonClass ν]
variable [NullSingletonClass μ]

theorem FourierJacobi.Measure.coordinates_determinant_ae_with_parameter {A : Type*} [MeasurableSpace A]
    (ρ : MeasureTheory.Measure A) (z : K) :
    ∀ᵐ p : A × (K × K) ∂ρ.prod (μ.prod ν),
      p.2.1 ≠ 0 ∧ p.2.2 ≠ 0 ∧ p.2.2 ^ 2 - p.2.1 * z ≠ 0 := by sorry
