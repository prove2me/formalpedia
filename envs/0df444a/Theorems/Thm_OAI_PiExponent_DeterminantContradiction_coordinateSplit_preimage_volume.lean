-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_coordinateSplit_preimage_volume
-- name    : OAI.PiExponent.DeterminantContradiction.coordinateSplit_preimage_volume
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T13:00:18.001641+00:00
-- url     : https://prove2.me/theorems/8f62b55b-5975-4cdf-8e47-51c36ea7737d
-- title:
--   Volume is preserved by finite coordinate splitting
-- statement:
--   For every natural number `m` and measurable set of real vectors indexed by `Fin (m+1)`, taking the preimage along the map that places the `Fin m` coordinates first and the real coordinate last preserves volume. This includes `m = 0` and does not impose boundedness or positivity.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open MeasureTheory

theorem OAI.PiExponent.DeterminantContradiction.coordinateSplit_preimage_volume (m : Nat) (s : Set (Fin (m + 1) → Real)) (hs : MeasurableSet s) :
    MeasureTheory.volume ((fun p : (Fin m → Real) × Real => fun i : Fin (m + 1) => Fin.lastCases p.2 p.1 i) ⁻¹' s) =
      MeasureTheory.volume s := by sorry
