-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_volume_succ_ENNReal
-- name    : OAI.PiExponent.DeterminantContradiction.simplex_volume_succ_ENNReal
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T15:30:57.853199+00:00
-- url     : https://prove2.me/theorems/202c6e48-0915-4a1b-9325-0528e55aeccf
-- title:
--   Simplex volume successor recurrence
-- statement:
--   The volume of the nonnegative coordinate simplex in dimension n+1 is its dimension-n volume divided by n+1.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
open MeasureTheory
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplex_volume_succ_ENNReal (n : Nat) :
    MeasureTheory.volume
      {x : Fin (n + 1) → Real | (∀ i, 0 ≤ x i) ∧
        (Finset.univ.sum fun i : Fin (n + 1) => x i) ≤ 1} =
      ENNReal.ofReal (1 / ((n + 1 : Nat) : Real)) *
        MeasureTheory.volume
          {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧
            (Finset.univ.sum fun i : Fin n => x i) ≤ 1} := by sorry
