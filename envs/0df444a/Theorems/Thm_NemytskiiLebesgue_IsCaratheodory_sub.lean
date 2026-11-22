-- Prove2me | Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_sub
-- name    : NemytskiiLebesgue.IsCaratheodory.sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:33:46.427904+00:00
-- url     : https://prove2.me/theorems/dae0772b-416b-4cb2-a22a-05d881be8da1
-- title:
--   Is Caratheodory: sub
-- statement:
--   The Is Caratheodory construction uses the sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Closure.lean#L86-L98
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Closure.lean#L86-L98

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Caratheodory
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Closure
set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter

theorem NemytskiiLebesgue.IsCaratheodory.sub
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [TopologicalSpace D]
    {F : Type*} [TopologicalSpace F]
    [Sub F] [ContinuousSub F]
    {f : Ω → D → F} (hf : IsCaratheodory f μ)
    {g : Ω → D → F} (hg : IsCaratheodory g μ) :
    IsCaratheodory (f - g) μ := by sorry
