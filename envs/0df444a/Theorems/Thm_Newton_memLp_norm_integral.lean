-- Prove2me | Theorems.Thm_Newton_memLp_norm_integral
-- name    : Newton.memLp_norm_integral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:12:03.237222+00:00
-- url     : https://prove2.me/theorems/90e36625-9c54-4f3f-b665-05c9e5a4b4d1
-- title:
--   Newton: mem Lp norm integral
-- statement:
--   The Newton construction uses the mem Lp norm integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/MeasureTheory/Function/LpSpace/Duality.lean#L1243-L1309
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/MeasureTheory/Function/LpSpace/Duality.lean#L1243-L1309

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sign
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_Newton_MeasureTheory_Integral_Holder
import Definitions.Def_Newton_MeasureTheory_Function_LpSpace_Duality
set_option autoImplicit false
open scoped ENNReal
open MeasureTheory Real Topology
open Newton
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {β : Type*} [MeasurableSpace β] {ν : Measure β}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem Newton.memLp_norm_integral
    {β : Type*} [MeasurableSpace β] {ν : Measure β}
    [SFinite μ] [SFinite ν]
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hp_ne_top : p ≠ ∞)
    {F : α → β → E}
    (hF_meas : AEStronglyMeasurable (Function.uncurry F) (μ.prod ν))
    (hF_prod : Integrable (Function.uncurry F) (μ.prod ν))
    (hF_memLp : ∀ᵐ y ∂ν, MemLp (fun x => F x y) p μ)
    (hF_norm : Integrable (fun y => (eLpNorm (fun x => F x y) p μ).toReal) ν) :
    MemLp (fun x => ‖∫ y, F x y ∂ν‖) p μ := by sorry
