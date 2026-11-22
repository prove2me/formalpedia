-- Prove2me | Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_real_mul
-- name    : NemytskiiLebesgue.IsCaratheodory.real_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:36:51.016633+00:00
-- url     : https://prove2.me/theorems/00e2cbb6-6c2d-4f85-86a4-42df2fc19498
-- title:
--   Is Caratheodory: real mul
-- statement:
--   The Is Caratheodory construction uses the real mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Closure.lean#L122-L128
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Closure.lean#L122-L128

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Caratheodory
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Closure
set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter

theorem NemytskiiLebesgue.IsCaratheodory.real_mul
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {m : ℕ} {D : Set ℝ^m}
    {f : Ω → D → ℝ} (hf : IsCaratheodory f μ)
    {g : Ω → D → ℝ} (hg : IsCaratheodory g μ) :
    IsCaratheodory (f * g) μ := by sorry
