-- Prove2me | Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_neg
-- name    : NemytskiiLebesgue.IsCaratheodory.neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:36:41.867873+00:00
-- url     : https://prove2.me/theorems/9b9b421d-76c3-4dec-a287-aee8ad568ec1
-- title:
--   Is Caratheodory: neg
-- statement:
--   The Is Caratheodory construction uses the neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Closure.lean#L73-L84
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Closure.lean#L73-L84

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Caratheodory
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Closure
set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter

theorem NemytskiiLebesgue.IsCaratheodory.neg
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [TopologicalSpace D]
    {F : Type*} [TopologicalSpace F]
    [Neg F] [ContinuousNeg F]
    {f : Ω → D → F} (hf : IsCaratheodory f μ) :
    IsCaratheodory (-f) μ := by sorry
