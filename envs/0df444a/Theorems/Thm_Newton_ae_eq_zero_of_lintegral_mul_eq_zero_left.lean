-- Prove2me | Theorems.Thm_Newton_ae_eq_zero_of_lintegral_mul_eq_zero_left
-- name    : Newton.ae_eq_zero_of_lintegral_mul_eq_zero_left
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:00:08.842244+00:00
-- url     : https://prove2.me/theorems/47d1b6e1-7ce2-450b-b399-4dbf4984fd2b
-- title:
--   Newton: ae eq zero of lintegral mul eq zero left
-- statement:
--   If the product `f * g` has zero integral and `g` is strictly positive a.e.,
--   then `f` vanishes a.e. (ℝ≥0∞-valued version).
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/Auxiliary.lean#L310-L347
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/Auxiliary.lean#L310-L347

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

theorem Newton.ae_eq_zero_of_lintegral_mul_eq_zero_left
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ≥0∞}
    (hg_pos : ∀ᵐ x ∂μ, 0 < g x)
    (hf_meas : AEMeasurable f μ) (hg_meas : AEMeasurable g μ)
    (h_int : ∫⁻ x, f x * g x ∂μ = 0) :
    f =ᵐ[μ] 0 := by sorry
