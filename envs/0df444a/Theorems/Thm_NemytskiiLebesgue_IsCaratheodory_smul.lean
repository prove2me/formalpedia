-- Prove2me | Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_smul
-- name    : NemytskiiLebesgue.IsCaratheodory.smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:36:50.98521+00:00
-- url     : https://prove2.me/theorems/3f097cd8-73c3-406c-915c-a448f4c5ca4c
-- title:
--   Is Caratheodory: smul
-- statement:
--   The Is Caratheodory construction uses the smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Closure.lean#L130-L142
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Closure.lean#L130-L142

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Caratheodory
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Closure
set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter

theorem NemytskiiLebesgue.IsCaratheodory.smul
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [TopologicalSpace D] {M : Type*} [TopologicalSpace M]
    {F : Type*} [TopologicalSpace F]
    [SMul M F] [ContinuousSMul M F]
    {f : Ω → D → M} (hf : IsCaratheodory f μ)
    {g : Ω → D → F} (hg : IsCaratheodory g μ) :
    IsCaratheodory (f • g) μ := by sorry
