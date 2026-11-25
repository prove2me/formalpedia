-- Prove2me | Theorems.Thm_Newton_lintegral_eq_zero_iff_ae_eq_zero
-- name    : Newton.lintegral_eq_zero_iff_ae_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:00:04.046908+00:00
-- url     : https://prove2.me/theorems/ace7088a-e2ad-4f6a-8f93-17d785d8a7ef
-- title:
--   Newton: lintegral eq zero iff ae eq zero
-- statement:
--   Characterization of vanishing `lintegral` in terms of a.e. vanishing (ℝ≥0∞-valued).
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/Auxiliary.lean#L302-L306
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/Auxiliary.lean#L302-L306

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

theorem Newton.lintegral_eq_zero_iff_ae_eq_zero
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) :
    (∫⁻ x, f x ∂μ = 0) ↔ f =ᵐ[μ] 0 := by sorry
