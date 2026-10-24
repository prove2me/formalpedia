-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_integratedScaledSimplexVolume
-- name    : OAI.PiExponent.DeterminantContradiction.integratedScaledSimplexVolume
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T13:24:44.906398+00:00
-- url     : https://prove2.me/theorems/1c06e229-ec64-47be-a5eb-6999cfbc2bce
-- title:
--   Integral of scaled simplex volumes
-- statement:
--   The integral over t in [0,1] of the n-dimensional simplex slice volumes with scale 1−t is 1/(n+1)!. Its proof applies the scaled-volume result to each slice and evaluates the resulting power integral.

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.integratedScaledSimplexVolume (n : Nat) :
    ∫⁻ t in Set.Icc (0 : Real) 1,
      MeasureTheory.volume
        {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1 - t}
      ∂MeasureTheory.volume =
    ENNReal.ofReal (1 / (Nat.factorial (n + 1) : Real)) := by sorry
