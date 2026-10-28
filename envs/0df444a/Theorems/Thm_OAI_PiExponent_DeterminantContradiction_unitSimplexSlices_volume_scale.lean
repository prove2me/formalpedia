-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unitSimplexSlices_volume_scale
-- name    : OAI.PiExponent.DeterminantContradiction.unitSimplexSlices_volume_scale
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T15:07:14.063975+00:00
-- url     : https://prove2.me/theorems/1b102273-ad45-4b9d-8216-eee053472604
-- title:
--   Scaling the unit simplex slice volume
-- statement:
--   For every `t` in `[0,1]`, the simplex slice cut off at `1 - t` has volume equal to the unit simplex volume times `(1 - t)^n`. Scaling the unit simplex by `1 - t` proves the statement; the endpoint `t = 1` and dimension zero require their usual determinant and zero-dimensional measure conventions.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open MeasureTheory

theorem OAI.PiExponent.DeterminantContradiction.unitSimplexSlices_volume_scale (n : Nat) (t : Real) (ht : t ∈ Set.Icc (0 : Real) 1) :
    MeasureTheory.volume
        {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧
          (Finset.univ.sum fun i : Fin n => x i) ≤ 1 - t} =
      MeasureTheory.volume
        {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧
          (Finset.univ.sum fun i : Fin n => x i) ≤ 1} *
        ENNReal.ofReal ((1 - t) ^ n) := by sorry
