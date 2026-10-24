-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexSliceVolume
-- name    : OAI.PiExponent.DeterminantContradiction.simplexSliceVolume
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T13:27:37.104276+00:00
-- url     : https://prove2.me/theorems/2b14ac93-492d-4212-8070-506834ace48d
-- title:
--   Volume of a scaled simplex slice
-- statement:
--   For n ≥ 0 and t in [0,1], the volume of the nonnegative simplex with coordinate sum at most 1 - t equals (1 - t)^n/n!. At t = 1 the slice has zero volume for positive n; when n = 0 the empty-dimensional slice and the formula both have volume 1.

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators
-- Proof route: identify the set as the dilation by 1 - t of the unit simplex in Fin n, apply the change-of-variables scaling law for Lebesgue volume, and use the standard unit-simplex volume formula. Handle the zero scale and n = 0 cases explicitly.

theorem OAI.PiExponent.DeterminantContradiction.simplexSliceVolume (n : Nat) (t : Real) (ht : t ∈ Set.Icc (0 : Real) 1) :
    MeasureTheory.volume
      {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1 - t} =
    ENNReal.ofReal (((1 - t) ^ n) / (Nat.factorial n : Real)) := by sorry
