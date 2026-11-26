-- Prove2me | Theorems.Thm_FourierJacobi_Measure_measurableSet_determinant_zero
-- name    : FourierJacobi.Measure.measurableSet_determinant_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:18:41.119455+00:00
-- url     : https://prove2.me/theorems/af889682-9591-5fa9-831c-f8ee75d05cef
-- title:
--   Measure: measurable Set determinant zero
-- statement:
--   The determinant polynomial's zero set is Borel, including z = 0.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/NullSets.lean#L56-L58
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/NullSets.lean#L56-L58

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

theorem FourierJacobi.Measure.measurableSet_determinant_zero (z : K) :
    MeasurableSet {p : K × K | p.2 ^ 2 - p.1 * z = 0} := by sorry
