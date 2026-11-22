-- Prove2me | Theorems.Thm_MeasurableConceptClass_hc_meas
-- name    : MeasurableConceptClass.hc_meas
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:35:07.332647+00:00
-- url     : https://prove2.me/theorems/fb03ecb9-6b43-4958-b1ae-77618f09afb0
-- title:
--   Measurable Concept Class: hc meas
-- statement:
--   The Measurable Concept Class construction uses the hc meas property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Measurability.lean#L88-L92
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Measurability.lean#L88-L92

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Symmetrization
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Measurability
set_option autoImplicit true
@[expose] public section
public section
universe u

theorem MeasurableConceptClass.hc_meas
    {X : Type u} [MeasurableSpace X]
    (C : ConceptClass X Bool) [h : MeasurableConceptClass X C] :
    ∀ c : Concept X Bool, Measurable c := by sorry
