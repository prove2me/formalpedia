-- Prove2me | Theorems.Thm_Newton_convolution_fiber_integrable_L2_L1
-- name    : Newton.convolution_fiber_integrable_L2_L1
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T00:56:27.01479+00:00
-- url     : https://prove2.me/theorems/dea09266-9d68-4048-b490-0833cafb84a9
-- title:
--   Newton: convolution fiber integrable L2 L1
-- statement:
--   Fiberwise integrability for L²×L¹ convolution kernels.
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/MeasureTheory/Integral/Tonelli.lean#L562-L878
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/MeasureTheory/Integral/Tonelli.lean#L562-L878

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Definitions.Def_Newton_MeasureTheory_Integral_Tonelli
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
open Newton
variable {G : Type*} [MeasurableSpace G]
variable {μ : Measure G}

theorem Newton.convolution_fiber_integrable_L2_L1
    {G : Type*} [NormedAddCommGroup G] [MeasurableSpace G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [SFinite μ] [μ.IsAddRightInvariant] [μ.IsNegInvariant]
    (f g : G → ℂ)
    (hf : MemLp f 2 μ) (hg : Integrable g μ) :
    ∀ᵐ x ∂μ, Integrable (fun y => f (x - y) * g y) μ := by sorry
