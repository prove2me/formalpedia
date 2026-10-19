-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_volume_smul_image_fin_real_zero
-- name    : OAI.PiExponent.DeterminantContradiction.volume_smul_image_fin_real_zero
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T03:24:06.41798+00:00
-- url     : https://prove2.me/theorems/117bff9e-be53-44d8-afe1-ee018e42ca3f
-- title:
--   Volume scaling under the zero map
-- statement:
--   For the zero scalar, the volume scaling identity holds in every finite real coordinate dimension, including dimension zero.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib

open scoped BigOperators Topology

theorem OAI.PiExponent.DeterminantContradiction.volume_smul_image_fin_real_zero
    (m : ℕ) (s : Set (Fin m → ℝ)) :
    ENNReal.toReal
        (MeasureTheory.volume ((fun x : Fin m → ℝ => (0 : ℝ) • x) '' s)) =
      (0 : ℝ) ^ m * ENNReal.toReal (MeasureTheory.volume s) := by sorry
