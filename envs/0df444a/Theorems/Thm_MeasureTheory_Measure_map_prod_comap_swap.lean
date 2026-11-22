-- Prove2me | Theorems.Thm_MeasureTheory_Measure_map_prod_comap_swap
-- name    : MeasureTheory.Measure.map_prod_comap_swap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:26:31.90375+00:00
-- url     : https://prove2.me/theorems/fd8ff9e0-5aa3-4e20-ba00-2be26d53db0e
-- title:
--   Measure: map prod comap swap
-- statement:
--   The law of $(X, Z)$ is the image of the law of $(Z,X)$.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/MeasureTheory/Measure/Prod.lean#L29-L38
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/MeasureTheory/Measure/Prod.lean#L29-L38

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

theorem MeasureTheory.Measure.map_prod_comap_swap (hX : Measurable X) (hZ : Measurable Z) (μ : Measure Ω) :
    (μ.map (fun ω ↦ (X ω, Z ω))).comap Prod.swap = μ.map (fun ω ↦ (Z ω, X ω)) := by sorry
