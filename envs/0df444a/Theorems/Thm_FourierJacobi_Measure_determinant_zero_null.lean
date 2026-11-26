-- Prove2me | Theorems.Thm_FourierJacobi_Measure_determinant_zero_null
-- name    : FourierJacobi.Measure.determinant_zero_null
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:18:44.602246+00:00
-- url     : https://prove2.me/theorems/45b5c469-5a61-442d-8de5-12da8420f1b3
-- title:
--   Measure: determinant zero null
-- statement:
--   Nullity of y²-xz=0 under actual product measures; unlike the original
--   integer tables this theorem covers z=0 as well.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/NullSets.lean#L71-L84
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/NullSets.lean#L71-L84

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

theorem FourierJacobi.Measure.determinant_zero_null (z : K) :
    (μ.prod ν) {p : K × K | p.2 ^ 2 - p.1 * z = 0} = 0 := by sorry
