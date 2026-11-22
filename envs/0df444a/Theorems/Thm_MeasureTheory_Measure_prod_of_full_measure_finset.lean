-- Prove2me | Theorems.Thm_MeasureTheory_Measure_prod_of_full_measure_finset
-- name    : MeasureTheory.Measure.prod_of_full_measure_finset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:26:42.671533+00:00
-- url     : https://prove2.me/theorems/dbb8e32e-faf0-4b9d-b249-b5e4b85a58c8
-- title:
--   Measure: prod of full measure finset
-- statement:
--   The Measure construction uses the prod of full measure finset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/MeasureTheory/Measure/Prod.lean#L50-L56
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/MeasureTheory/Measure/Prod.lean#L50-L56

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

theorem MeasureTheory.Measure.prod_of_full_measure_finset {μ : Measure α} {ν : Measure β} [SigmaFinite ν]
    {A : Finset α} {B : Finset β} (hA : μ Aᶜ = 0) (hB : ν Bᶜ = 0) :
    (μ.prod ν) (A ×ˢ B : Finset (α × β))ᶜ = 0 := by sorry
