-- Prove2me | Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_aestronglyMeas_nemytskii
-- name    : NemytskiiLebesgue.IsCaratheodory.aestronglyMeas_nemytskii
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:34:31.534446+00:00
-- url     : https://prove2.me/theorems/d8000da5-ac3b-4cd9-bd19-b5957b327cd8
-- title:
--   Is Caratheodory: aestrongly Meas nemytskii
-- statement:
--   The Is Caratheodory construction uses the aestrongly Meas nemytskii property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Frechet.lean#L142-L148
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Frechet.lean#L142-L148

module
public import Mathlib.Analysis.Calculus.MeanValue
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Continuity
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Frechet
set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter
open scoped ENNReal Topology

theorem NemytskiiLebesgue.IsCaratheodory.aestronglyMeas_nemytskii
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {m k : ℕ}
    {f : Ω → ℝ^m → ℝ^k} (hf : IsCaratheodory f μ)
    {u : Ω → ℝ^m} {p : ℝ} (hup : MemLp u ↱p μ) :
    AEStronglyMeasurable (fun ω : Ω => f ω (u ω)) μ := by sorry
