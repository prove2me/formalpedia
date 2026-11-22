-- Prove2me | Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_fst
-- name    : NemytskiiLebesgue.IsCaratheodory.fst
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:34:24.135356+00:00
-- url     : https://prove2.me/theorems/5a6172fd-8c54-4099-a5c7-73aedc99d18d
-- title:
--   Is Caratheodory: fst
-- statement:
--   The Is Caratheodory construction uses the fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Closure.lean#L329-L336
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Closure.lean#L329-L336

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Caratheodory
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Closure
set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter

theorem NemytskiiLebesgue.IsCaratheodory.fst
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [TopologicalSpace D]
    {F : Type*} [TopologicalSpace F]
    {G : Type*} [TopologicalSpace G]
    {f : Ω → D → F × G} (hf : IsCaratheodory f μ) :
    IsCaratheodory (fun ω : Ω => fun x : D => (f ω x).fst) μ := by sorry
