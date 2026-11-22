-- Prove2me | Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_real_sub
-- name    : NemytskiiLebesgue.IsCaratheodory.real_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:36:47.08222+00:00
-- url     : https://prove2.me/theorems/3e5a89cb-0d9e-4ace-a116-592b70213fc4
-- title:
--   Is Caratheodory: real sub
-- statement:
--   The Is Caratheodory construction uses the real sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Closure.lean#L100-L106
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Closure.lean#L100-L106

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Caratheodory
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Closure
set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter

theorem NemytskiiLebesgue.IsCaratheodory.real_sub
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {m k : ℕ} {D : Set ℝ^m}
    {f : Ω → D → ℝ^k} (hf : IsCaratheodory f μ)
    {g : Ω → D → ℝ^k} (hg : IsCaratheodory g μ) :
    IsCaratheodory (f - g) μ := by sorry
