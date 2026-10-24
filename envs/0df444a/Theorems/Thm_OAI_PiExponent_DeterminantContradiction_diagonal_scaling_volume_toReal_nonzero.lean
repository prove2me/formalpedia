-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_diagonal_scaling_volume_toReal_nonzero
-- name    : OAI.PiExponent.DeterminantContradiction.diagonal_scaling_volume_toReal_nonzero
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T15:01:37.845901+00:00
-- url     : https://prove2.me/theorems/a31dcbb7-fd17-4374-85ac-9d9a3ff90c30
-- title:
--   Volume scaling under nonzero diagonal maps
-- statement:
--   For a measurable set in finite-dimensional real coordinate space, scaling each coordinate by a nonzero real factor multiplies its volume by the absolute value of the product of those factors.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.diagonal_scaling_volume_toReal_nonzero {m : Nat} (w : Fin m → Real) (hw : ∀ i, w i ≠ 0) (s : Set (Fin m → Real)) (hs : MeasurableSet s) :
    (MeasureTheory.volume ((fun x : Fin m → Real => fun i => w i * x i) '' s)).toReal =
      |(∏ i : Fin m, w i)| * (MeasureTheory.volume s).toReal := by sorry
