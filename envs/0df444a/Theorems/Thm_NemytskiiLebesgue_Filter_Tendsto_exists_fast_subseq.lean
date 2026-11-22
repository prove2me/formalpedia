-- Prove2me | Theorems.Thm_NemytskiiLebesgue_Filter_Tendsto_exists_fast_subseq
-- name    : NemytskiiLebesgue.Filter.Tendsto.exists_fast_subseq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:34:07.032086+00:00
-- url     : https://prove2.me/theorems/ef808bf4-a3b4-465f-973c-ea2c5d9245b6
-- title:
--   Tendsto: exists fast subseq
-- statement:
--   The Tendsto construction uses the exists fast subseq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Continuity.lean#L183-L191
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Continuity.lean#L183-L191

module
public import Mathlib.MeasureTheory.Function.UnifTight
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Caratheodory
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Continuity
set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter
open scoped NNReal ENNReal Topology

theorem NemytskiiLebesgue.Filter.Tendsto.exists_fast_subseq
    {f : ℕ → ℝ≥0∞} (hf : Tendsto f atTop (𝓝 0)) :
    ∃ s : ℕ → ℕ, StrictMono s ∧ ∀ n : ℕ, f (s n) ≤ (1 / 2 : ℝ≥0∞) ^ n := by sorry
