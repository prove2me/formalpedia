-- Prove2me | Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_of_stronglyMeasurable
-- name    : NemytskiiLebesgue.IsCaratheodory.of_stronglyMeasurable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:36:39.56409+00:00
-- url     : https://prove2.me/theorems/3925d59b-9555-4aa9-80a7-5ff6777248f2
-- title:
--   Is Caratheodory: of strongly Measurable
-- statement:
--   The Is Caratheodory construction uses the of strongly Measurable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Closure.lean#L34-L40
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Closure.lean#L34-L40

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Caratheodory
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Closure
set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter

theorem NemytskiiLebesgue.IsCaratheodory.of_stronglyMeasurable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {D : Type*} [TopologicalSpace D]
    {F : Type*} [TopologicalSpace F]
    {f : Ω → F} (hf : StronglyMeasurable f) :
    IsCaratheodory (fun ω : Ω => fun _ : D => f ω) μ := by sorry
