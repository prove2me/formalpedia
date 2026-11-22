-- Prove2me | Theorems.Thm_NemytskiiLebesgue_aestronglyMeasurable_composition_of_stronglyMeasurable
-- name    : NemytskiiLebesgue.aestronglyMeasurable_composition_of_stronglyMeasurable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:33:29.607179+00:00
-- url     : https://prove2.me/theorems/26518f90-4197-45ff-94ba-0e74ac7f2d7d
-- title:
--   Nemytskii Lebesgue: aestrongly Measurable composition of strongly Measurable
-- statement:
--   The Nemytskii Lebesgue construction uses the aestrongly Measurable composition of strongly Measurable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Caratheodory.lean#L44-L83
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Caratheodory.lean#L44-L83

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

theorem NemytskiiLebesgue.aestronglyMeasurable_composition_of_stronglyMeasurable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [TopologicalSpace D]
    {F : Type*} [TopologicalSpace F] [PseudoMetrizableSpace F]
    {f : Ω → D → F} (hf : ∀ x : D, AEStronglyMeasurable (f · x) μ) (hf' : ∀ᵐ ω : Ω ∂μ, Continuous
      (f ω))
    {g : Ω → D} (hg : StronglyMeasurable g) :
    AEStronglyMeasurable (fun ω : Ω => f ω (g ω)) μ := by sorry
