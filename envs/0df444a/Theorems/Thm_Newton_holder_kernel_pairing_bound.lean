-- Prove2me | Theorems.Thm_Newton_holder_kernel_pairing_bound
-- name    : Newton.holder_kernel_pairing_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:38:11.170547+00:00
-- url     : https://prove2.me/theorems/65b33e2b-4a12-490b-8dd4-106dec54769b
-- title:
--   Newton: holder kernel pairing bound
-- statement:
--   Auxiliary estimate used in the proof of Minkowski's integral inequality.  It bounds the pairing
--   between the norm of a fibrewise integral and a dual element of `L^q`.
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/MeasureTheory/Integral/Holder.lean#L671-L987
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/MeasureTheory/Integral/Holder.lean#L671-L987

import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Real.ConjExponents
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Definitions.Def_Newton_MeasureTheory_Integral_Holder
set_option autoImplicit false
open MeasureTheory ENNReal NNReal
open scoped ENNReal BigOperators
open Newton
variable {α : Type*} [MeasurableSpace α]
variable {μ : Measure α}
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
variable {β : Type*} [MeasurableSpace β]
variable {ν : Measure β}

theorem Newton.holder_kernel_pairing_bound
    [NormedSpace ℝ E] [SFinite μ] [SFinite ν]
    (p q : ℝ≥0∞) (hpq : IsConjugateExponent p q)
    {F : α → β → E} {φ : α → ℝ}
    (hF_meas : AEStronglyMeasurable (Function.uncurry F) (μ.prod ν))
    (hF_prod : Integrable (Function.uncurry F) (μ.prod ν))
    (hF_memLp : ∀ᵐ y ∂ν, MemLp (fun x => F x y) p μ)
    (hF_norm : Integrable (fun y => (eLpNorm (fun x => F x y) p μ).toReal) ν)
    (hφ_mem : MemLp φ q μ) :
    |∫ x, ‖∫ y, F x y ∂ν‖ * φ x ∂μ|
      ≤ (eLpNorm φ q μ).toReal *
        ∫ y, (eLpNorm (fun x => F x y) p μ).toReal ∂ν := by sorry
