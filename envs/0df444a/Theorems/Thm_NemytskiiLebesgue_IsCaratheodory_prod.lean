-- Prove2me | Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_prod
-- name    : NemytskiiLebesgue.IsCaratheodory.prod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:37:08.661623+00:00
-- url     : https://prove2.me/theorems/cf53c46e-c77d-489e-887a-369622dee553
-- title:
--   Is Caratheodory: prod
-- statement:
--   The Is Caratheodory construction uses the prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Closure.lean#L313-L327
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Closure.lean#L313-L327

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Caratheodory
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Closure
set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter

theorem NemytskiiLebesgue.IsCaratheodory.prod
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [TopologicalSpace D]
    {F : Type*} [TopologicalSpace F]
    {G : Type*} [TopologicalSpace G]
    {f : Ω → D → F} (hf : IsCaratheodory f μ)
    {g : Ω → D → G} (hg : IsCaratheodory g μ) :
    IsCaratheodory (fun ω : Ω => fun x : D => (f ω x, g ω x)) μ := by sorry
