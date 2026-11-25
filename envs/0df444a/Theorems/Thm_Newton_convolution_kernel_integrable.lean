-- Prove2me | Theorems.Thm_Newton_convolution_kernel_integrable
-- name    : Newton.convolution_kernel_integrable
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:13:42.78895+00:00
-- url     : https://prove2.me/theorems/f595e13a-0ac2-47d7-a3b4-f17c45083a6e
-- title:
--   Newton: convolution kernel integrable
-- statement:
--   Integrability of the convolution kernel assuming the factors themselves are integrable. This is the
--   basic input needed for the convolution estimates below.
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/Minkowski.lean#L236-L355
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/Minkowski.lean#L236-L355

import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_Newton_MeasureTheory_Integral_Holder
import Definitions.Def_Newton_MeasureTheory_Function_LpSpace_Duality
import Definitions.Def_Newton_Analysis_Convolution_Minkowski
set_option autoImplicit false
open MeasureTheory ENNReal NNReal
open scoped ENNReal
open Newton
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β}
variable {E : Type*} [NormedAddCommGroup E]
variable {G : Type*}
variable [NormedAddCommGroup G] [MeasurableSpace G]
variable [MeasurableAdd₂ G] [MeasurableNeg G]
variable (μ : Measure G) [SFinite μ] [μ.IsAddRightInvariant]

theorem Newton.convolution_kernel_integrable
    (f g : G → ℂ)
    (hf : Integrable f μ) (hg : Integrable g μ) :
    Integrable (fun q : G × G => f (q.1 - q.2) * g q.2) (μ.prod μ) := by sorry
