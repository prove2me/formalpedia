-- Prove2me | Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_sup
-- name    : NemytskiiLebesgue.IsCaratheodory.sup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:34:17.596181+00:00
-- url     : https://prove2.me/theorems/b6a539fa-da63-4b60-bc28-899b1caa1c7e
-- title:
--   Is Caratheodory: sup
-- statement:
--   The Is Caratheodory construction uses the sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Closure.lean#L218-L230
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Closure.lean#L218-L230

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Caratheodory
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Closure
set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter

theorem NemytskiiLebesgue.IsCaratheodory.sup
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [TopologicalSpace D]
    {F : Type*} [TopologicalSpace F]
    [Max F] [ContinuousSup F]
    {f : Ω → D → F} (hf : IsCaratheodory f μ)
    {g : Ω → D → F} (hg : IsCaratheodory g μ) :
    IsCaratheodory (f ⊔ g) μ := by sorry
