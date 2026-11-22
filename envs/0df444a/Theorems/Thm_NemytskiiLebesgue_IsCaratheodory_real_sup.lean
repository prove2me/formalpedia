-- Prove2me | Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_real_sup
-- name    : NemytskiiLebesgue.IsCaratheodory.real_sup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:36:55.837841+00:00
-- url     : https://prove2.me/theorems/e8e1837a-28c1-4bc9-a2ea-096e7511e5e7
-- title:
--   Is Caratheodory: real sup
-- statement:
--   The Is Caratheodory construction uses the real sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Closure.lean#L232-L238
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Closure.lean#L232-L238

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Caratheodory
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Closure
set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter

theorem NemytskiiLebesgue.IsCaratheodory.real_sup
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {m : ℕ} {D : Set ℝ^m}
    {f : Ω → D → ℝ} (hf : IsCaratheodory f μ)
    {g : Ω → D → ℝ} (hg : IsCaratheodory g μ) :
    IsCaratheodory (f ⊔ g) μ := by sorry
