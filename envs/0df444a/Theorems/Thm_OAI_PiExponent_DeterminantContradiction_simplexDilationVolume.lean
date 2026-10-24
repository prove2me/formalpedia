-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexDilationVolume
-- name    : OAI.PiExponent.DeterminantContradiction.simplexDilationVolume
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T13:33:11.985575+00:00
-- url     : https://prove2.me/theorems/1b5921ab-a3a2-4138-9de9-fe4bab8a96a3
-- title:
--   Volume scaling for a coordinate simplex
-- statement:
--   For c ≥ 0, scaling the coordinate simplex by c multiplies its n-dimensional volume by c^n. This includes c = 0 and n = 0.

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplexDilationVolume (n : Nat) (c : Real) (hc : 0 ≤ c) :
    MeasureTheory.volume
      {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ c} =
    ENNReal.ofReal c ^ n *
      MeasureTheory.volume
        {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} := by sorry
