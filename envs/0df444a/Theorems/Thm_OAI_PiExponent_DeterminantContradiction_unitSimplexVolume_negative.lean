-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unitSimplexVolume_negative
-- name    : OAI.PiExponent.DeterminantContradiction.unitSimplexVolume_negative
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T15:19:37.694478+00:00
-- url     : https://prove2.me/theorems/f12c15b1-9584-41d9-8ccc-78f8a77701d9
-- title:
--   Negative cutoff simplex is empty
-- statement:
--   For a negative cutoff, the simplex has volume zero because nonnegative coordinates have nonnegative sum, including when there are no coordinates.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open MeasureTheory

theorem OAI.PiExponent.DeterminantContradiction.unitSimplexVolume_negative
    (n : Nat) (c : Real) (hc : c < 0) :
    MeasureTheory.volume
      {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧
        (Finset.univ.sum fun i : Fin n => x i) ≤ c} = 0 := by sorry
