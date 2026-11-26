-- Prove2me | Theorems.Thm_FourierJacobi_Measure_restrict_goodCoordinates
-- name    : FourierJacobi.Measure.restrict_goodCoordinates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:40:01.104634+00:00
-- url     : https://prove2.me/theorems/885a22ff-45bc-4d76-9206-f2695d3e9186
-- title:
--   Measure: restrict good Coordinates
-- statement:
--   Removing the exceptional set preserves the measure itself, hence every
--   Bochner integral and every integrability assertion for this product measure.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/NullSets.lean#L111-L114
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/NullSets.lean#L111-L114

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

theorem FourierJacobi.Measure.restrict_goodCoordinates (z : K) :
    (μ.prod ν).restrict {p : K × K |
      p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ p.2 ^ 2 - p.1 * z ≠ 0} = μ.prod ν := by sorry
