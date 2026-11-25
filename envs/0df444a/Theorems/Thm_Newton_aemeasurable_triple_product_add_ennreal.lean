-- Prove2me | Theorems.Thm_Newton_aemeasurable_triple_product_add_ennreal
-- name    : Newton.aemeasurable_triple_product_add_ennreal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:22:31.556366+00:00
-- url     : https://prove2.me/theorems/3b54f37e-787f-49d5-ba28-a9cd9e6f6b0c
-- title:
--   Newton: aemeasurable triple product add ennreal
-- statement:
--   The Newton construction uses the aemeasurable triple product add ennreal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/MeasureTheory/Integral/Tonelli.lean#L947-L980
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/MeasureTheory/Integral/Tonelli.lean#L947-L980

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Definitions.Def_Newton_MeasureTheory_Integral_Tonelli
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
open Newton
variable {G : Type*} [MeasurableSpace G]
variable {μ : Measure G}

theorem Newton.aemeasurable_triple_product_add_ennreal
    {G : Type*} [MeasurableSpace G] [AddCommGroup G] [TopologicalSpace G]
    [MeasurableAdd₂ G] {μ : Measure G} [μ.IsAddHaarMeasure] [SFinite μ] {f g φ : G → ℂ}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hφ : AEStronglyMeasurable φ μ) :
    AEMeasurable
      (fun zy : G × G => (‖g zy.2‖₊ : ℝ≥0∞) * ‖φ (zy.1 + zy.2)‖₊ * ‖f zy.1‖₊)
      (μ.prod μ) := by sorry
