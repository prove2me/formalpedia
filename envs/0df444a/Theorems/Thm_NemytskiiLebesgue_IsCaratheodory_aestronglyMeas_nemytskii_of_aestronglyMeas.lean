-- Prove2me | Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_aestronglyMeas_nemytskii_of_aestronglyMeas
-- name    : NemytskiiLebesgue.IsCaratheodory.aestronglyMeas_nemytskii_of_aestronglyMeas
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:33:33.733549+00:00
-- url     : https://prove2.me/theorems/f7effb12-32aa-4d10-a66a-0354091c0a07
-- title:
--   Is Caratheodory: aestrongly Meas nemytskii of aestrongly Meas
-- statement:
--   The Is Caratheodory construction uses the aestrongly Meas nemytskii of aestrongly Meas property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Caratheodory.lean#L101-L111
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Caratheodory.lean#L101-L111

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

theorem NemytskiiLebesgue.IsCaratheodory.aestronglyMeas_nemytskii_of_aestronglyMeas
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [TopologicalSpace D]
    {F : Type*} [TopologicalSpace F] [PseudoMetrizableSpace F]
    {f : Ω → D → F} (hf : IsCaratheodory f μ)
    {g : Ω → D} (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (fun ω : Ω => f ω (g ω)) μ := by sorry
