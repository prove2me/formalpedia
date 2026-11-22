-- Prove2me | Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_aestronglyMeas_nemytskii_of_aeMeas_real
-- name    : NemytskiiLebesgue.IsCaratheodory.aestronglyMeas_nemytskii_of_aeMeas_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:33:36.137836+00:00
-- url     : https://prove2.me/theorems/a7608e6c-86e0-4b80-ae8b-4db56a741ad3
-- title:
--   Is Caratheodory: aestrongly Meas nemytskii of ae Meas real
-- statement:
--   The Is Caratheodory construction uses the aestrongly Meas nemytskii of ae Meas real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Caratheodory.lean#L113-L119
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Caratheodory.lean#L113-L119

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

theorem NemytskiiLebesgue.IsCaratheodory.aestronglyMeas_nemytskii_of_aeMeas_real
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {m k : ℕ} {D : Set ℝ^m}
    {f : Ω → D → ℝ^k} (hf : IsCaratheodory f μ)
    {g : Ω → D} (hg : AEMeasurable g μ) :
    AEStronglyMeasurable (fun ω : Ω => f ω (g ω)) μ := by sorry
