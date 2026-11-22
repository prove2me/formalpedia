-- Prove2me | Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_const_smul
-- name    : NemytskiiLebesgue.IsCaratheodory.const_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:36:48.729006+00:00
-- url     : https://prove2.me/theorems/bb5513b8-fa3e-47cd-9ac3-d112d2366dfd
-- title:
--   Is Caratheodory: const smul
-- statement:
--   The Is Caratheodory construction uses the const smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Closure.lean#L144-L155
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Closure.lean#L144-L155

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Caratheodory
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Closure
set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter

theorem NemytskiiLebesgue.IsCaratheodory.const_smul
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [TopologicalSpace D] {M : Type*}
    {F : Type*} [TopologicalSpace F]
    [SMul M F] [ContinuousConstSMul M F]
    {f : Ω → D → F} (hf : IsCaratheodory f μ) (c : M) :
    IsCaratheodory (c • f) μ := by sorry
