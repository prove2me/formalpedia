-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolume_zero_v2
-- name    : OAI.PiExponent.DeterminantContradiction.simplexVolume_zero_v2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T14:53:24.131081+00:00
-- url     : https://prove2.me/theorems/9a885b37-e7d4-4649-98eb-9086bfadb2f1
-- title:
--   Zero-dimensional simplex volume
-- statement:
--   In dimension zero, the coordinate function space has one point, so the simplex has volume 1, equal to the reciprocal of 0 factorial.

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplexVolume_zero_v2 :
    MeasureTheory.volume
        {x : Fin 0 → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} =
      ENNReal.ofReal (1 / (Nat.factorial 0 : Real)) := by sorry
