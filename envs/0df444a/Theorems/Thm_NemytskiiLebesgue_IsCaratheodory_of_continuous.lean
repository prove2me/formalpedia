-- Prove2me | Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_of_continuous
-- name    : NemytskiiLebesgue.IsCaratheodory.of_continuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:36:42.600179+00:00
-- url     : https://prove2.me/theorems/8fc0d6f8-d3ca-453e-afc2-aa40446ae144
-- title:
--   Is Caratheodory: of continuous
-- statement:
--   The Is Caratheodory construction uses the of continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Closure.lean#L42-L49
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Closure.lean#L42-L49

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Caratheodory
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Closure
set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter

theorem NemytskiiLebesgue.IsCaratheodory.of_continuous
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [TopologicalSpace D]
    {F : Type*} [TopologicalSpace F]
    {f : D → F} (hf : Continuous f) :
    IsCaratheodory (fun _ : Ω => fun x : D => f x) μ := by sorry
