-- Prove2me | Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_inv
-- name    : NemytskiiLebesgue.IsCaratheodory.inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:36:50.339207+00:00
-- url     : https://prove2.me/theorems/f6af2f02-20a3-4607-b438-2517161e2848
-- title:
--   Is Caratheodory: inv
-- statement:
--   The Is Caratheodory construction uses the inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Closure.lean#L157-L168
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Closure.lean#L157-L168

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Caratheodory
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Closure
set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter

theorem NemytskiiLebesgue.IsCaratheodory.inv
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [TopologicalSpace D]
    {F : Type*} [TopologicalSpace F]
    [Inv F] [ContinuousInv F]
    {f : Ω → D → F} (hf : IsCaratheodory f μ) :
    IsCaratheodory (f⁻¹) μ := by sorry
