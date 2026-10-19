-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_diagonal_map_volume_of_measurable_finite
-- name    : OAI.PiExponent.DeterminantContradiction.diagonal_map_volume_of_measurable_finite
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T03:27:58.285347+00:00
-- url     : https://prove2.me/theorems/88450439-9a77-4776-b343-c7f00f47f375
-- title:
--   Volume scaling for a positive diagonal map
-- statement:
--   For a measurable set of finite volume in finite-dimensional real coordinate space, a coordinatewise map with positive scale factors multiplies its volume by the product of those factors.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib

open scoped BigOperators Topology

theorem OAI.PiExponent.DeterminantContradiction.diagonal_map_volume_of_measurable_finite (m : ℕ) (w : Fin m → ℝ) (hw : ∀ i, 0 < w i) (s : Set (Fin m → ℝ)) (hs : MeasurableSet s) (hfin : MeasureTheory.volume s < ⊤) : ENNReal.toReal (MeasureTheory.volume ((fun x i => w i * x i) '' s)) = (∏ i : Fin m, w i) * ENNReal.toReal (MeasureTheory.volume s) := by sorry
