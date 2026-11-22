-- Prove2me | Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_real_div
-- name    : NemytskiiLebesgue.IsCaratheodory.real_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:36:52.675448+00:00
-- url     : https://prove2.me/theorems/17496cea-6bb2-4392-b5be-e257e9906dae
-- title:
--   Is Caratheodory: real div
-- statement:
--   The Is Caratheodory construction uses the real div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Closure.lean#L184-L196
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Closure.lean#L184-L196

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Caratheodory
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Closure
set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter

theorem NemytskiiLebesgue.IsCaratheodory.real_div
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {m : ℕ} {D : Set ℝ^m}
    {f : Ω → D → ℝ} (hf : IsCaratheodory f μ)
    {g : Ω → D → ℝ} (hg : IsCaratheodory g μ)
    (hg0 : ∀ᵐ ω ∂μ, ∀ x : D, g ω x ≠ 0) :
    IsCaratheodory (f / g) μ := by sorry
