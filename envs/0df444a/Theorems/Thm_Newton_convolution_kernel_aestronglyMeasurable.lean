-- Prove2me | Theorems.Thm_Newton_convolution_kernel_aestronglyMeasurable
-- name    : Newton.convolution_kernel_aestronglyMeasurable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:13:58.247863+00:00
-- url     : https://prove2.me/theorems/343fa512-583a-4b32-8e43-1c76ad9fac32
-- title:
--   Newton: convolution kernel aestrongly Measurable
-- statement:
--   Almost everywhere measurability of the convolution kernel produced from `L^p` data. This lemma
--   packages the hypotheses needed to apply Minkowski's integral inequality in the Young inequality
--   arguments.
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/Minkowski.lean#L202-L230
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/Minkowski.lean#L202-L230

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

theorem Newton.convolution_kernel_aestronglyMeasurable
    (f g : G → ℂ)
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (fun q : G × G => f (q.1 - q.2) * g q.2) (μ.prod μ) := by sorry
