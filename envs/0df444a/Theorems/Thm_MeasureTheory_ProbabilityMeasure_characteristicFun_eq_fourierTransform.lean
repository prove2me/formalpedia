-- Prove2me | Theorems.Thm_MeasureTheory_ProbabilityMeasure_characteristicFun_eq_fourierTransform
-- name    : MeasureTheory.ProbabilityMeasure.characteristicFun_eq_fourierTransform
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T12:32:40.099388+00:00
-- url     : https://prove2.me/theorems/5f15359a-6803-4df0-891b-8766f1ecba67
-- title:
--   LeanLevy: MeasureTheory.ProbabilityMeasure.characteristicFun_eq_fourierTransform
-- statement:
--   Exact theorem signature transcribed from the pinned LeanLevy source. The source section variable is made explicit; the proof remains open.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Probability/Characteristic.lean#L88

import Mathlib
import Definitions.Def_LeanLevy_Probability_Characteristic
open MeasureTheory Complex ComplexConjugate MeasureTheory.ProbabilityMeasure

theorem MeasureTheory.ProbabilityMeasure.characteristicFun_eq_fourierTransform (μ : ProbabilityMeasure ℝ) (ξ : ℝ) :
    characteristicFun μ ξ = FiniteMeasure.fourierTransform μ.toFiniteMeasure ξ := by sorry
