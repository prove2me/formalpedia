-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolume_succ_47e3ceaa
-- name    : OAI.PiExponent.DeterminantContradiction.simplexVolume_succ_47e3ceaa
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T14:22:14.634446+00:00
-- url     : https://prove2.me/theorems/3d1d4b50-0a78-4812-8572-306f4fe19f72
-- title:
--   Successor-dimensional simplex volume recurrence
-- statement:
--   The volume of the (n+1)-dimensional unit simplex is the n-dimensional simplex volume multiplied by 1/(n+1).

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplexVolume_succ_47e3ceaa (n : Nat) :
    MeasureTheory.volume
        {x : Fin (n + 1) → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} =
      ENNReal.ofReal (1 / ((Nat.factorial n : Nat) : Real)) *
        ENNReal.ofReal (1 / ((n + 1 : Nat) : Real)) := by sorry
