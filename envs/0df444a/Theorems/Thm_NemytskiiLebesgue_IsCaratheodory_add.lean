-- Prove2me | Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_add
-- name    : NemytskiiLebesgue.IsCaratheodory.add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:33:47.327259+00:00
-- url     : https://prove2.me/theorems/7dfe4cd2-5847-4806-a396-49e7e3927754
-- title:
--   Is Caratheodory: add
-- statement:
--   The Is Caratheodory construction uses the add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Closure.lean#L51-L63
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Closure.lean#L51-L63

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Caratheodory
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Closure
set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter

theorem NemytskiiLebesgue.IsCaratheodory.add
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [TopologicalSpace D]
    {F : Type*} [TopologicalSpace F]
    [Add F] [ContinuousAdd F]
    {f : Ω → D → F} (hf : IsCaratheodory f μ)
    {g : Ω → D → F} (hg : IsCaratheodory g μ) :
    IsCaratheodory (f + g) μ := by sorry
