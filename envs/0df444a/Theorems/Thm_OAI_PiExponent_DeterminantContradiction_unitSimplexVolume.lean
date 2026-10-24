-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unitSimplexVolume
-- name    : OAI.PiExponent.DeterminantContradiction.unitSimplexVolume
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T13:33:27.639133+00:00
-- url     : https://prove2.me/theorems/83507ab4-a0b9-4071-8fc9-3239f5c88396
-- title:
--   Volume of the unit coordinate simplex
-- statement:
--   For every natural number n, the set of nonnegative vectors in Fin n whose coordinates sum to at most 1 has volume 1/n!. The formula includes n = 0, where the empty-dimensional set has volume 1.

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.unitSimplexVolume (n : Nat) :
    MeasureTheory.volume
      {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} =
    ENNReal.ofReal (1 / (Nat.factorial n : Real)) := by sorry
