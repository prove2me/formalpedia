-- Prove2me | Theorems.Thm_NemytskiiLebesgue_normSMulSelf_isCaratheodory
-- name    : NemytskiiLebesgue.normSMulSelf_isCaratheodory
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:35:19.982189+00:00
-- url     : https://prove2.me/theorems/45b9ae0a-b7f3-4373-9e23-330dd2443453
-- title:
--   Nemytskii Lebesgue: norm SMul Self is Caratheodory
-- statement:
--   The Nemytskii Lebesgue construction uses the norm SMul Self is Caratheodory property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Caratheodory.lean#L39-L42
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Caratheodory.lean#L39-L42

module
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Basic
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Caratheodory
set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory TopologicalSpace Filter
open scoped Topology

theorem NemytskiiLebesgue.normSMulSelf_isCaratheodory
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n : ℕ} :
    IsCaratheodory (@normSMulSelf Ω n) μ := by sorry
