-- Prove2me | Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_const
-- name    : NemytskiiLebesgue.IsCaratheodory.const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:36:36.521849+00:00
-- url     : https://prove2.me/theorems/59ef5772-bb87-4753-9510-f1f225c7f01f
-- title:
--   Is Caratheodory: const
-- statement:
--   The Is Caratheodory construction uses the const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Closure.lean#L25-L32
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Closure.lean#L25-L32

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Caratheodory
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Closure
set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter

theorem NemytskiiLebesgue.IsCaratheodory.const
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [TopologicalSpace D]
    {F : Type*} [TopologicalSpace F]
    (c : F) :
    IsCaratheodory (fun _ : Ω => fun _ : D => c) μ := by sorry
