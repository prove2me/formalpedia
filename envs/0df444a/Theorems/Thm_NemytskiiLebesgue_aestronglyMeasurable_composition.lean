-- Prove2me | Theorems.Thm_NemytskiiLebesgue_aestronglyMeasurable_composition
-- name    : NemytskiiLebesgue.aestronglyMeasurable_composition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:33:35.153035+00:00
-- url     : https://prove2.me/theorems/ae530aea-bd2d-45c8-acc6-2ba64d04f4f7
-- title:
--   Nemytskii Lebesgue: aestrongly Measurable composition
-- statement:
--   The Nemytskii Lebesgue construction uses the aestrongly Measurable composition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Caratheodory.lean#L85-L99
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Caratheodory.lean#L85-L99

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

theorem NemytskiiLebesgue.aestronglyMeasurable_composition
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [TopologicalSpace D]
    {F : Type*} [TopologicalSpace F] [PseudoMetrizableSpace F]
    {f : Ω → D → F} (hf : ∀ x : D, AEStronglyMeasurable (f · x) μ) (hf' : ∀ᵐ ω : Ω ∂μ, Continuous
      (f ω))
    {g : Ω → D} (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (fun ω : Ω => f ω (g ω)) μ := by sorry
