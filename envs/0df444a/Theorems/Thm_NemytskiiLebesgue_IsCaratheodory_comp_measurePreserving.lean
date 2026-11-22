-- Prove2me | Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_comp_measurePreserving
-- name    : NemytskiiLebesgue.IsCaratheodory.comp_measurePreserving
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:37:01.202295+00:00
-- url     : https://prove2.me/theorems/2507bfe7-6362-4b6d-9282-7a07a5794b47
-- title:
--   Is Caratheodory: comp measure Preserving
-- statement:
--   The Is Caratheodory construction uses the comp measure Preserving property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Closure.lean#L276-L287
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Closure.lean#L276-L287

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Caratheodory
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Closure
set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter

theorem NemytskiiLebesgue.IsCaratheodory.comp_measurePreserving
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {μ' : Measure Ω'}
    {D : Type*} [TopologicalSpace D]
    {F : Type*} [TopologicalSpace F]
    {f : Ω → D → F} (hf : IsCaratheodory f μ)
    {g : Ω' → Ω} (hg : MeasurePreserving g μ' μ) :
    IsCaratheodory (f ∘ g) μ' := by sorry
