-- Prove2me | Theorems.Thm_Newton_aemeasurable_smul_measure_of_aemeasurable
-- name    : Newton.aemeasurable_smul_measure_of_aemeasurable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:14:33.259368+00:00
-- url     : https://prove2.me/theorems/43501a44-8f88-42a1-bb69-41ac94df7842
-- title:
--   Newton: aemeasurable smul measure of aemeasurable
-- statement:
--   Transport `AEMeasurable` across a positive scalar multiple of a measure.
--   If `f` is a.e.-measurable w.r.t. `μ`, then it is also a.e.-measurable w.r.t. `c • μ`.
--   This simple helper is used to avoid threading measurability through `map` equalities.
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/Bounds.lean#L41-L54
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/Bounds.lean#L41-L54

import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Definitions.Def_Newton_Analysis_Convolution_Basic
import Definitions.Def_Newton_Analysis_Convolution_Minkowski
import Definitions.Def_Newton_Analysis_Convolution_Bounds
set_option autoImplicit false
open MeasureTheory Complex NNReal
open scoped ENNReal ContDiff Pointwise
open Newton
variable {n : ℕ}

theorem Newton.aemeasurable_smul_measure_of_aemeasurable
    {α : Type*} [MeasurableSpace α]
    (f : α → ℝ≥0∞) (μ : Measure α) (c : ℝ≥0∞)
    (hf : AEMeasurable f μ) : AEMeasurable f (c • μ) := by sorry
