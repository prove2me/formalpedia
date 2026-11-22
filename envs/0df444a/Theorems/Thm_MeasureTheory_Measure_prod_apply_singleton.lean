-- Prove2me | Theorems.Thm_MeasureTheory_Measure_prod_apply_singleton
-- name    : MeasureTheory.Measure.prod_apply_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:25:08.513936+00:00
-- url     : https://prove2.me/theorems/1ad5228a-24e5-4acf-afa8-f6ab84aacad5
-- title:
--   Measure: prod apply singleton
-- statement:
--   The Measure construction uses the prod apply singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/MeasureTheory/Measure/Prod.lean#L40-L43
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/MeasureTheory/Measure/Prod.lean#L40-L43

module
public import Mathlib.MeasureTheory.Measure.Prod
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Measure_Prod
set_option autoImplicit true
@[expose] public section
public section
open Function
open scoped ENNReal NNReal
open MeasureTheory MeasureTheory.Measure
variable {Ω α β γ : Type*} [MeasurableSpace Ω]
  [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] {X : Ω → α} {Y : Ω
    → β} {Z : Ω → γ}

theorem MeasureTheory.Measure.prod_apply_singleton {α β : Type*} {_ : MeasurableSpace α} {_ : MeasurableSpace β}
    (μ : Measure α) (ν : Measure β) [SigmaFinite ν] (x : α × β) :
    (μ.prod ν) {x} = μ {x.1} * ν {x.2} := by sorry
