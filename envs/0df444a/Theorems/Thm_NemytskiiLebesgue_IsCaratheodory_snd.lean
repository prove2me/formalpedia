-- Prove2me | Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_snd
-- name    : NemytskiiLebesgue.IsCaratheodory.snd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:34:23.903513+00:00
-- url     : https://prove2.me/theorems/e716b736-d781-417b-87a5-6b45038c5e3b
-- title:
--   Is Caratheodory: snd
-- statement:
--   The Is Caratheodory construction uses the snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Closure.lean#L338-L345
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Closure.lean#L338-L345

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Caratheodory
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Closure
set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter

theorem NemytskiiLebesgue.IsCaratheodory.snd
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [TopologicalSpace D]
    {F : Type*} [TopologicalSpace F]
    {G : Type*} [TopologicalSpace G]
    {f : Ω → D → F × G} (hf : IsCaratheodory f μ) :
    IsCaratheodory (fun ω : Ω => fun x : D => (f ω x).snd) μ := by sorry
