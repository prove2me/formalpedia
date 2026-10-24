-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unitSimplexVolume_succ
-- name    : OAI.PiExponent.DeterminantContradiction.unitSimplexVolume_succ
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T13:57:58.487658+00:00
-- url     : https://prove2.me/theorems/5bf48635-53ce-4381-ac76-4e00a49dddb0
-- title:
--   Successor-dimensional unit simplex volume by slicing
-- statement:
--   Slicing the (n+1)-dimensional coordinate simplex by its last coordinate gives volume 1 divided by n! times n+1. The slice at t is a scaled n-dimensional simplex, with scale 1-t; integrating its n-dimensional volume over 0 ≤ t ≤ 1 yields the stated value.

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.unitSimplexVolume_succ (n : Nat) :
    MeasureTheory.volume
      {x : Fin (n + 1) → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} =
    ENNReal.ofReal
      (1 / ((Nat.factorial n : Real) * ((n + 1 : Nat) : Real))) := by sorry
