-- Prove2me | Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_real_pow_nat
-- name    : NemytskiiLebesgue.IsCaratheodory.real_pow_nat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:36:56.437035+00:00
-- url     : https://prove2.me/theorems/80ec5589-a9e5-4ff1-b8bb-5653b4a2c739
-- title:
--   Is Caratheodory: real pow nat
-- statement:
--   The Is Caratheodory construction uses the real pow nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Closure.lean#L211-L216
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Closure.lean#L211-L216

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Caratheodory
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Closure
set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter

theorem NemytskiiLebesgue.IsCaratheodory.real_pow_nat
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {m : ℕ} {D : Set ℝ^m}
    {f : Ω → D → ℝ} (hf : IsCaratheodory f μ) (n : ℕ) :
    IsCaratheodory (f ^ n) μ := by sorry
