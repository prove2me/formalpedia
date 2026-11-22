-- Prove2me | Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_div
-- name    : NemytskiiLebesgue.IsCaratheodory.div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:34:12.505692+00:00
-- url     : https://prove2.me/theorems/c3c7a15a-9cbd-4a99-8a1e-30bb461c4dbb
-- title:
--   Is Caratheodory: div
-- statement:
--   The Is Caratheodory construction uses the div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Closure.lean#L170-L182
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Closure.lean#L170-L182

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Caratheodory
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Closure
set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter

theorem NemytskiiLebesgue.IsCaratheodory.div
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [TopologicalSpace D]
    {F : Type*} [TopologicalSpace F]
    [Div F] [ContinuousDiv F]
    {f : Ω → D → F} (hf : IsCaratheodory f μ)
    {g : Ω → D → F} (hg : IsCaratheodory g μ) :
    IsCaratheodory (f / g) μ := by sorry
