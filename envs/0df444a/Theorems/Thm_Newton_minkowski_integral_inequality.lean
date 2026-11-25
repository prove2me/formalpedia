-- Prove2me | Theorems.Thm_Newton_minkowski_integral_inequality
-- name    : Newton.minkowski_integral_inequality
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:37:54.559173+00:00
-- url     : https://prove2.me/theorems/59f95c4e-8eca-4715-b20a-394b57f0f1c4
-- title:
--   Newton: minkowski integral inequality
-- statement:
--   **Minkowski's integral inequality (general form with eLpNorm).**
--
--   For 1 ≤ p < ∞ and measurable F : α × β → E,
--     ‖∫ F(·, y) dν(y)‖_{L^p(μ)} ≤ ∫ ‖F(·, y)‖_{L^p(μ)} dν(y)
--
--   This is the key inequality for proving Young's inequality for convolution.
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/Minkowski.lean#L46-L186
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/Minkowski.lean#L46-L186

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
variable [SFinite μ] [SFinite ν]

theorem Newton.minkowski_integral_inequality
    [NormedSpace ℝ E] (p : ℝ≥0∞) (hp : 1 ≤ p) (hp_ne_top : p ≠ ∞) (F : α → β → E)
    (hF : AEStronglyMeasurable (Function.uncurry F) (μ.prod ν))
    (hF_prod : Integrable (Function.uncurry F) (μ.prod ν))
    (hF_int : ∀ᵐ y ∂ν, Integrable (fun x => F x y) μ)
    (hF_memLp : ∀ᵐ y ∂ν, MemLp (fun x => F x y) p μ)
    (hF_norm : Integrable (fun y => (eLpNorm (fun x => F x y) p μ).toReal) ν) :
    eLpNorm (fun x => ∫ y, F x y ∂ν) p μ ≤
    ENNReal.ofReal (∫ y, (eLpNorm (fun x => F x y) p μ).toReal ∂ν) := by sorry
