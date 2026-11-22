-- Prove2me | Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_norm
-- name    : NemytskiiLebesgue.IsCaratheodory.norm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:34:28.772236+00:00
-- url     : https://prove2.me/theorems/514bddde-0c72-4362-a2df-fef2dec6afd4
-- title:
--   Is Caratheodory: norm
-- statement:
--   The Is Caratheodory construction uses the norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Closure.lean#L289-L299
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Closure.lean#L289-L299

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Caratheodory
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Closure
set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter

theorem NemytskiiLebesgue.IsCaratheodory.norm
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [TopologicalSpace D]
    {F : Type*} [NormedAddCommGroup F]
    {f : Ω → D → F} (hf : IsCaratheodory f μ) :
    IsCaratheodory (‖f · ·‖) μ := by sorry
