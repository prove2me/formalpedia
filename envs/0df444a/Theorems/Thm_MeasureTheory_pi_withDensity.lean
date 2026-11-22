-- Prove2me | Theorems.Thm_MeasureTheory_pi_withDensity
-- name    : MeasureTheory.pi_withDensity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:51:33.660065+00:00
-- url     : https://prove2.me/theorems/3d10df39-78c2-4dd9-ba2b-5742eec263b9
-- title:
--   Measure Theory: pi with Density
-- statement:
--   **The `pi`-`withDensity` bridge.** A finite product of measures, each given a
--   density, is the product measure with the product density:
--   `Measure.pi (fun i => (μ i).withDensity (g i))
--     = (Measure.pi μ).withDensity (fun x => ∏ i, g i (x i))`.
--   The `pi` analogue of `MeasureTheory.prod_withDensity`. Proved by `Measure.pi_eq`
--   on rectangles, using `lintegral_fintype_prod_eq_prod` to factor the
--   product-density integral over the rectangle.
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/MeasureTheory/LintegralFintypeProd.lean#L84-L111
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/MeasureTheory/LintegralFintypeProd.lean#L84-L111

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

theorem MeasureTheory.pi_withDensity {E : ι → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} (μ : (i : ι) → Measure (E i)) [∀ i, SigmaFinite (μ i)]
    (g : (i : ι) → E i → ℝ≥0∞) (hg : ∀ i, Measurable (g i))
    [∀ i, SigmaFinite ((μ i).withDensity (g i))] :
    Measure.pi (fun i => (μ i).withDensity (g i))
      = (Measure.pi μ).withDensity (fun x => ∏ i, g i (x i)) := by sorry
