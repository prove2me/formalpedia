-- Prove2me | Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_pow_nat
-- name    : NemytskiiLebesgue.IsCaratheodory.pow_nat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:34:19.036059+00:00
-- url     : https://prove2.me/theorems/2613ba1a-1462-4b53-8a69-02081a012964
-- title:
--   Is Caratheodory: pow nat
-- statement:
--   The Is Caratheodory construction uses the pow nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Closure.lean#L198-L209
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Closure.lean#L198-L209

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Caratheodory
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Closure
set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter

theorem NemytskiiLebesgue.IsCaratheodory.pow_nat
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [TopologicalSpace D]
    {F : Type*} [TopologicalSpace F]
    [Monoid F] [ContinuousMul F]
    {f : Ω → D → F} (hf : IsCaratheodory f μ) (n : ℕ) :
    IsCaratheodory (f ^ n) μ := by sorry
