-- Prove2me | Theorems.Thm_FourierJacobi_Measure_integersHaar_integralShell
-- name    : FourierJacobi.Measure.integersHaar_integralShell
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:45:37.700919+00:00
-- url     : https://prove2.me/theorems/0d8f38e0-e473-5f69-918f-b91a37004a56
-- title:
--   Measure: integers Haar integral Shell
-- statement:
--   The Measure construction uses the integers Haar integral Shell property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/LocalHaar.lean#L173-L181
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/LocalHaar.lean#L173-L181

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

theorem FourierJacobi.Measure.integersHaar_integralShell (n : ℕ) :
    integersHaar K (integralShell K n) =
      (residueCardinality K : ℝ≥0∞)⁻¹ ^ n -
        (residueCardinality K : ℝ≥0∞)⁻¹ ^ (n + 1) := by sorry
