-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weighted_lattice_box_measure
-- name    : OAI.PiExponent.DeterminantContradiction.weighted_lattice_box_measure
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T09:23:59.641686+00:00
-- url     : https://prove2.me/theorems/047da649-9897-42f1-b7f9-38ff06ad90b0
-- title:
--   Measurability and volume of one weighted lattice box
-- statement:
--   For each lattice vector, the corresponding weighted box is measurable and has volume equal to the product of its coordinate weights. A proof can identify the box with a finite product of intervals, apply the product-volume formula, and compute each interval's length using `0 < w i`. In dimension zero, the product is empty and the volume is one.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib

open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.weighted_lattice_box_measure
    (m : ℕ) (w : Fin m → ℝ) (hw : ∀ i, 0 < w i)
    (a : Fin m → ℕ) :
    MeasurableSet
        {x : Fin m → ℝ | ∀ i,
          w i * (a i : ℝ) ≤ x i ∧ x i < w i * ((a i : ℝ) + 1)} ∧
      MeasureTheory.volume
          {x : Fin m → ℝ | ∀ i,
            w i * (a i : ℝ) ≤ x i ∧ x i < w i * ((a i : ℝ) + 1)} =
        ∏ i : Fin m, ENNReal.ofReal (w i) := by sorry
