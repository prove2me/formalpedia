-- Prove2me | Theorems.Thm_MeasureTheory_MeasurePreserving_identDistrib
-- name    : MeasureTheory.MeasurePreserving.identDistrib
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:28:33.845459+00:00
-- url     : https://prove2.me/theorems/c71c8401-4ab9-4bca-aa8c-64eccad7f1db
-- title:
--   Measure Preserving: ident Distrib
-- statement:
--   The Measure Preserving construction uses the ident Distrib property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/IdentDistrib.lean#L149-L158
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Probability/IdentDistrib.lean#L149-L158

module
public import Mathlib.Probability.IdentDistrib
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Constructions_Pi
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_IdentDistrib
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MeasureTheory Measure Filter Set
open scoped Topology MeasureTheory ENNReal NNReal
attribute [symm] ProbabilityTheory.IdentDistrib.symm
variable {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  [MeasurableSpace δ]
open ProbabilityTheory
variable {μ : Measure α} {ν : Measure β} {f f' : α → γ} {g g' : β → γ} {s : Set γ}

theorem MeasureTheory.MeasurePreserving.identDistrib {α β γ : Type*} {X : β
  → γ} {f : α → β}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] {μ : Measure α}
    {ν : Measure β} (hf : MeasurePreserving f μ ν) (hX : AEMeasurable X ν) :
    IdentDistrib X (X ∘ f) ν μ := by sorry
