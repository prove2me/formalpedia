-- Prove2me | Theorems.Thm_Newton_lintegral_mul_mul_le_three_holder
-- name    : Newton.lintegral_mul_mul_le_three_holder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:56:58.594882+00:00
-- url     : https://prove2.me/theorems/00494d22-3532-48af-8f63-1626369b2026
-- title:
--   Newton: lintegral mul mul le three holder
-- statement:
--   The Newton construction uses the lintegral mul mul le three holder property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/Auxiliary.lean#L16-L127
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/Auxiliary.lean#L16-L127

import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Topology.MetricSpace.Holder
import Definitions.Def_Newton_MeasureTheory_Integral_Tonelli
import Definitions.Def_Newton_Analysis_Convolution_Auxiliary
set_option autoImplicit false
open MeasureTheory Complex NNReal
open scoped ENNReal Topology ContDiff ComplexConjugate
open Newton
variable {n : ℕ}

theorem Newton.lintegral_mul_mul_le_three_holder
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g h : α → ℝ≥0∞}
    {p q r : ℝ≥0∞}
    (hpqr : 1 / p + 1 / q + 1 / r = 1)
    (hp_top : p ≠ ⊤) (hq_top : q ≠ ⊤) (hr_top : r ≠ ⊤)
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) (hh : AEMeasurable h μ) :
    ∫⁻ x, f x * g x * h x ∂μ ≤
      (∫⁻ x, f x ^ p.toReal ∂μ) ^ (1/p.toReal) *
      (∫⁻ x, g x ^ q.toReal ∂μ) ^ (1/q.toReal) *
      (∫⁻ x, h x ^ r.toReal ∂μ) ^ (1/r.toReal) := by sorry
