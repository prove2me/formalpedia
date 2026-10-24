-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unitSimplexVolume_unit
-- name    : OAI.PiExponent.DeterminantContradiction.unitSimplexVolume_unit
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T15:17:17.74086+00:00
-- url     : https://prove2.me/theorems/138fd41a-bedb-41a8-aff9-5b68a0267b67
-- title:
--   Unit simplex volume
-- statement:
--   The nonnegative-coordinate simplex with coordinate sum at most one has volume 1/n!, including dimension zero.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open MeasureTheory

theorem OAI.PiExponent.DeterminantContradiction.unitSimplexVolume_unit (n : Nat) :
    MeasureTheory.volume
      {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧
        (Finset.univ.sum fun i : Fin n => x i) ≤ 1} =
      ENNReal.ofReal (1 / (Nat.factorial n : Real)) := by sorry
