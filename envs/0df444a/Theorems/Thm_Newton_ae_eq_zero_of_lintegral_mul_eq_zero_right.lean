-- Prove2me | Theorems.Thm_Newton_ae_eq_zero_of_lintegral_mul_eq_zero_right
-- name    : Newton.ae_eq_zero_of_lintegral_mul_eq_zero_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:25:04.933247+00:00
-- url     : https://prove2.me/theorems/43c8c3ef-bd3f-49d4-8acf-8bd493cf5fc1
-- title:
--   Newton: ae eq zero of lintegral mul eq zero right
-- statement:
--   Symmetric version of `ae_eq_zero_of_lintegral_mul_eq_zero_left`.
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/Auxiliary.lean#L350-L362
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/Auxiliary.lean#L350-L362

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

theorem Newton.ae_eq_zero_of_lintegral_mul_eq_zero_right
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ≥0∞}
    (hf_pos : ∀ᵐ x ∂μ, 0 < f x)
    (hf_meas : AEMeasurable f μ) (hg_meas : AEMeasurable g μ)
    (h_int : ∫⁻ x, f x * g x ∂μ = 0) :
    g =ᵐ[μ] 0 := by sorry
