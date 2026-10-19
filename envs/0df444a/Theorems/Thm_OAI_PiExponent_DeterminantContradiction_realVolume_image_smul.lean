-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_realVolume_image_smul
-- name    : OAI.PiExponent.DeterminantContradiction.realVolume_image_smul
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T08:01:33.99575+00:00
-- url     : https://prove2.me/theorems/328dcf9b-5460-4b31-9447-24b760384d6b
-- title:
--   Volume scaling under positive dilation
-- statement:
--   For a measurable set in Fin n → ℝ, positive scalar dilation multiplies its real Lebesgue volume by r^n.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open scoped BigOperators Topology

theorem OAI.PiExponent.DeterminantContradiction.realVolume_image_smul
    (n : ℕ) (r : ℝ) (hr : 0 < r) (s : Set (Fin n → ℝ))
    (hs : MeasurableSet s) :
    ENNReal.toReal (MeasureTheory.volume ((fun x : Fin n → ℝ => r • x) '' s)) =
      r ^ n * ENNReal.toReal (MeasureTheory.volume s) := by sorry
