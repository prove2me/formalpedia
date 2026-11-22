-- Prove2me | Theorems.Thm_MeasureTheory_lintegral_fin_nat_prod_eq_prod
-- name    : MeasureTheory.lintegral_fin_nat_prod_eq_prod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:51:33.264996+00:00
-- url     : https://prove2.me/theorems/e6488751-1cd8-437b-8d17-8f6c5884db1b
-- title:
--   Measure Theory: lintegral fin nat prod eq prod
-- statement:
--   **Tonelli for a product over `Fin n` (`lintegral`).** The lower integral of a
--   product of single-coordinate functions over `Measure.pi` is the product of the
--   lower integrals. Proved by induction on `n` (`measurePreserving_piFinSuccAbove`
--   splits off the `0`-th coordinate; `lintegral_prod_mul` factors the resulting
--   product).
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/MeasureTheory/LintegralFintypeProd.lean#L42-L63
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/MeasureTheory/LintegralFintypeProd.lean#L42-L63

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
set_option backward.isDefEq.respectTransparency false

theorem MeasureTheory.lintegral_fin_nat_prod_eq_prod {n : ℕ} {E : Fin n → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : Fin n) → Measure (E i)}
    [∀ i, SigmaFinite (μ i)]
    (f : (i : Fin n) → E i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : Fin n) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by sorry
