-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_volume_toReal_mono_of_subset
-- name    : OAI.PiExponent.DeterminantContradiction.volume_toReal_mono_of_subset
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T11:54:52.82498+00:00
-- url     : https://prove2.me/theorems/ceab564b-fb44-48f4-b6f5-5b69c46898a4
-- title:
--   Real measure is monotone for finite upper measure
-- statement:
--   For a measure and sets s ⊆ t, monotonicity gives μ s ≤ μ t; if μ t is finite, monotonicity of ENNReal.toReal yields the claimed real inequality. This removes the measure-comparison step from the parent. It follows from measure monotonicity and the finite-upper-bound form of toReal monotonicity, and does not require measurable sets.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

theorem OAI.PiExponent.DeterminantContradiction.volume_toReal_mono_of_subset
    {α : Type} [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    {s t : Set α} (hsub : s ⊆ t) (ht : μ t ≠ ⊤) :
    ENNReal.toReal (μ s) ≤ ENNReal.toReal (μ t) := by sorry
