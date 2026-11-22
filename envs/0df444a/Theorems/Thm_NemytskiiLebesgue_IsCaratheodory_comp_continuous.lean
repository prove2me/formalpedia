-- Prove2me | Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_comp_continuous
-- name    : NemytskiiLebesgue.IsCaratheodory.comp_continuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:33:46.795026+00:00
-- url     : https://prove2.me/theorems/32315d93-922e-4660-bc02-c0527027e187
-- title:
--   Is Caratheodory: comp continuous
-- statement:
--   The Is Caratheodory construction uses the comp continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Closure.lean#L262-L274
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Closure.lean#L262-L274

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Caratheodory
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Closure
set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter

theorem NemytskiiLebesgue.IsCaratheodory.comp_continuous
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [TopologicalSpace D]
    {F : Type*} [TopologicalSpace F]
    {G : Type*} [TopologicalSpace G]
    {f : Ω → D → F} (hf : IsCaratheodory f μ)
    {g : F → G} (hg : Continuous g) :
    IsCaratheodory (g <| f · ·) μ := by sorry
