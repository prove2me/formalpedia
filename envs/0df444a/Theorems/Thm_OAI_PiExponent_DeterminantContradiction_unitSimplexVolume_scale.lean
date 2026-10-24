-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unitSimplexVolume_scale
-- name    : OAI.PiExponent.DeterminantContradiction.unitSimplexVolume_scale
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T15:18:25.277729+00:00
-- url     : https://prove2.me/theorems/d1925011-2598-4509-8b66-b3f661ac7349
-- title:
--   Scaling the simplex cutoff
-- statement:
--   For every nonnegative cutoff, simplex volume is the unit simplex volume multiplied by cⁿ. The zero cutoff and zero-dimensional cases are included.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open MeasureTheory

theorem OAI.PiExponent.DeterminantContradiction.unitSimplexVolume_scale
    (n : Nat) (c : Real) (hc : 0 ≤ c) :
    MeasureTheory.volume
      {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧
        (Finset.univ.sum fun i : Fin n => x i) ≤ c} =
      ENNReal.ofReal (c ^ n) *
        MeasureTheory.volume
          {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧
            (Finset.univ.sum fun i : Fin n => x i) ≤ 1} := by sorry
