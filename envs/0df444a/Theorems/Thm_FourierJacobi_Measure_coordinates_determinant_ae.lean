-- Prove2me | Theorems.Thm_FourierJacobi_Measure_coordinates_determinant_ae
-- name    : FourierJacobi.Measure.coordinates_determinant_ae
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:27:59.221302+00:00
-- url     : https://prove2.me/theorems/41c84361-be3b-4840-8624-cc590ccdd914
-- title:
--   Measure: coordinates determinant ae
-- statement:
--   Both additive coordinates and the determinant are nonzero almost
--   everywhere. This is the precise finite-coordinate locus of the tables.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/NullSets.lean#L90-L107
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/NullSets.lean#L90-L107

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

theorem FourierJacobi.Measure.coordinates_determinant_ae (z : K) :
    ∀ᵐ p : K × K ∂μ.prod ν, p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ p.2 ^ 2 - p.1 * z ≠ 0 := by sorry
