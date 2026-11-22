-- Prove2me | Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_nnnorm
-- name    : NemytskiiLebesgue.IsCaratheodory.nnnorm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:37:06.300086+00:00
-- url     : https://prove2.me/theorems/d82120ec-c2c9-4e0a-88bf-bfc4af7baf5c
-- title:
--   Is Caratheodory: nnnorm
-- statement:
--   The Is Caratheodory construction uses the nnnorm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Closure.lean#L301-L311
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Closure.lean#L301-L311

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Caratheodory
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Closure
set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter

theorem NemytskiiLebesgue.IsCaratheodory.nnnorm
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [TopologicalSpace D]
    {F : Type*} [NormedAddCommGroup F]
    {f : Ω → D → F} (hf : IsCaratheodory f μ) :
    IsCaratheodory (‖f · ·‖₊) μ := by sorry
