-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_volume_smul_image_fin_real
-- name    : OAI.PiExponent.DeterminantContradiction.volume_smul_image_fin_real
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T03:18:53.866182+00:00
-- url     : https://prove2.me/theorems/9abd44b2-fc84-44e8-bb34-5e6abb98c0c1
-- title:
--   Volume scaling for scalar images in finite real coordinate spaces
-- statement:
--   For any set in a finite real coordinate space, scalar multiplication by a nonnegative T scales its volume by T to the dimension, including zero-dimensional and zero-scaling boundary cases.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib

open scoped BigOperators Topology

theorem OAI.PiExponent.DeterminantContradiction.volume_smul_image_fin_real
    (m : ℕ) (T : ℝ) (hT : 0 ≤ T) (s : Set (Fin m → ℝ)) :
    ENNReal.toReal (MeasureTheory.volume ((fun x : Fin m → ℝ => T • x) '' s)) =
      T ^ m * ENNReal.toReal (MeasureTheory.volume s) := by sorry
