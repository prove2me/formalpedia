-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_volume_smul_image_fin_real_of_ne_zero
-- name    : OAI.PiExponent.DeterminantContradiction.volume_smul_image_fin_real_of_ne_zero
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T03:23:51.48667+00:00
-- url     : https://prove2.me/theorems/e39baaa6-6ca5-45de-8fe7-b0c921e76273
-- title:
--   Volume scaling under nonzero scalar multiplication
-- statement:
--   For a nonnegative, nonzero scalar, scaling any set in a finite real coordinate space scales its volume by the scalar raised to the dimension.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib

open scoped BigOperators Topology

theorem OAI.PiExponent.DeterminantContradiction.volume_smul_image_fin_real_of_ne_zero
    (m : ℕ) (T : ℝ) (hT : 0 ≤ T) (hT0 : T ≠ 0) (s : Set (Fin m → ℝ)) :
    ENNReal.toReal (MeasureTheory.volume ((fun x : Fin m → ℝ => T • x) '' s)) =
      T ^ m * ENNReal.toReal (MeasureTheory.volume s) := by sorry
