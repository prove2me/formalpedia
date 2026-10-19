-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_volume_smul_image
-- name    : OAI.PiExponent.DeterminantContradiction.volume_smul_image
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T21:16:59.629976+00:00
-- url     : https://prove2.me/theorems/0bea3e13-5dc8-475c-b514-dc737b719906
-- title:
--   Volume scaling for scalar images in finite dimension
-- statement:
--   For a measurable set in `Fin k → ℝ`, scaling every coordinate by positive `U` multiplies its real-valued volume by `U^k`. The zero-dimensional case gives factor one; for measurable sets of infinite volume, both `toReal` values are zero.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib

open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.volume_smul_image (k : ℕ) (U : ℝ) (hU : 0 < U)
    (s : Set (Fin k → ℝ)) (hs : MeasurableSet s) :
    (MeasureTheory.volume ((fun x : Fin k → ℝ => U • x) '' s)).toReal =
      (U ^ k) * (MeasureTheory.volume s).toReal := by sorry
