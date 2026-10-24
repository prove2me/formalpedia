-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unitSimplexVolume_cutoff
-- name    : OAI.PiExponent.DeterminantContradiction.unitSimplexVolume_cutoff
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T15:07:28.065793+00:00
-- url     : https://prove2.me/theorems/e43bd540-b3fd-4996-85c8-f25cc4f38c38
-- title:
--   Volume of a simplex with arbitrary cutoff
-- statement:
--   For a nonnegative cutoff c, the n-dimensional simplex of nonnegative coordinates whose sum is at most c has volume c^n/n!. For a negative cutoff it is empty. This includes n=0: the volume is one when c is nonnegative and zero otherwise. Prove by scaling from the unit simplex and induction or slicing; the zero-dimensional case must be handled explicitly.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open MeasureTheory

theorem OAI.PiExponent.DeterminantContradiction.unitSimplexVolume_cutoff (n : Nat) (c : Real) :
    MeasureTheory.volume
      {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧
        (Finset.univ.sum fun i : Fin n => x i) ≤ c} =
      (if 0 ≤ c then ENNReal.ofReal (c ^ n / (Nat.factorial n : Real)) else 0) := by sorry
