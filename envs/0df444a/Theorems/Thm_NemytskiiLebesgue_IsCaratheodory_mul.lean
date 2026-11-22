-- Prove2me | Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_mul
-- name    : NemytskiiLebesgue.IsCaratheodory.mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:33:49.628805+00:00
-- url     : https://prove2.me/theorems/8f06b0f1-1aaf-4ce1-adba-52d0e397c63f
-- title:
--   Is Caratheodory: mul
-- statement:
--   The Is Caratheodory construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Closure.lean#L108-L120
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Closure.lean#L108-L120

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Caratheodory
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Closure
set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter

theorem NemytskiiLebesgue.IsCaratheodory.mul
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [TopologicalSpace D]
    {F : Type*} [TopologicalSpace F]
    [Mul F] [ContinuousMul F]
    {f : Ω → D → F} (hf : IsCaratheodory f μ)
    {g : Ω → D → F} (hg : IsCaratheodory g μ) :
    IsCaratheodory (f * g) μ := by sorry
