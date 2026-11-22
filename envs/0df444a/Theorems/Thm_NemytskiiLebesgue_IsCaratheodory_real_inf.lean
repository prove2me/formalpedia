-- Prove2me | Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_real_inf
-- name    : NemytskiiLebesgue.IsCaratheodory.real_inf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:37:12.216388+00:00
-- url     : https://prove2.me/theorems/afee5daf-a3f9-4a7f-8904-23be330b54e0
-- title:
--   Is Caratheodory: real inf
-- statement:
--   The Is Caratheodory construction uses the real inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Closure.lean#L254-L260
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Closure.lean#L254-L260

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Caratheodory
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Closure
set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter

theorem NemytskiiLebesgue.IsCaratheodory.real_inf
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {m : ℕ} {D : Set ℝ^m}
    {f : Ω → D → ℝ} (hf : IsCaratheodory f μ)
    {g : Ω → D → ℝ} (hg : IsCaratheodory g μ) :
    IsCaratheodory (f ⊓ g) μ := by sorry
