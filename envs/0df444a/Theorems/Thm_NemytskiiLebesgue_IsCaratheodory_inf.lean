-- Prove2me | Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_inf
-- name    : NemytskiiLebesgue.IsCaratheodory.inf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:34:16.673179+00:00
-- url     : https://prove2.me/theorems/c806e39e-02ae-43cf-80dd-5605fbf0a604
-- title:
--   Is Caratheodory: inf
-- statement:
--   The Is Caratheodory construction uses the inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Closure.lean#L240-L252
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Closure.lean#L240-L252

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Caratheodory
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Closure
set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter

theorem NemytskiiLebesgue.IsCaratheodory.inf
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [TopologicalSpace D]
    {F : Type*} [TopologicalSpace F]
    [Min F] [ContinuousInf F]
    {f : Ω → D → F} (hf : IsCaratheodory f μ)
    {g : Ω → D → F} (hg : IsCaratheodory g μ) :
    IsCaratheodory (f ⊓ g) μ := by sorry
