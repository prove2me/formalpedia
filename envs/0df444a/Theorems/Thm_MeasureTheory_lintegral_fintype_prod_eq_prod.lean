-- Prove2me | Theorems.Thm_MeasureTheory_lintegral_fintype_prod_eq_prod
-- name    : MeasureTheory.lintegral_fintype_prod_eq_prod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:51:33.926894+00:00
-- url     : https://prove2.me/theorems/71c70345-1b53-4b88-8404-6092189db841
-- title:
--   Measure Theory: lintegral fintype prod eq prod
-- statement:
--   **Tonelli for a product over a finite index (`lintegral`).** The general-index
--   version, transferred from `lintegral_fin_nat_prod_eq_prod` via `equivFin`.
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/MeasureTheory/LintegralFintypeProd.lean#L67-L75
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/MeasureTheory/LintegralFintypeProd.lean#L67-L75

module
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Constructions.Pi
public import Definitions.Def_BornVolumeLean_MeasureTheory_LintegralFintypeProd
set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory
open scoped ENNReal
open MeasureTheory
variable {ι : Type*} [Fintype ι]

theorem MeasureTheory.lintegral_fintype_prod_eq_prod {E : ι → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : ι) → Measure (E i)} [∀ i, SigmaFinite (μ i)]
    (f : (i : ι) → E i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : ι) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by sorry
