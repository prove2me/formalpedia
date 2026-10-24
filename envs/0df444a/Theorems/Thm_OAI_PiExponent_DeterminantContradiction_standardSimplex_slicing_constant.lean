-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standardSimplex_slicing_constant
-- name    : OAI.PiExponent.DeterminantContradiction.standardSimplex_slicing_constant
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T13:04:31.898698+00:00
-- url     : https://prove2.me/theorems/667213d6-87d7-48f2-be4a-560543c8e489
-- title:
--   Simplex volume by slicing with one dilation factor
-- statement:
--   The volume of the standard `(n+1)`-simplex is the lower integral over its last coordinate of the `n`-dimensional unit-simplex volume scaled once by the remaining radius `(1 - t)^n`. Slicing and the finite-dimensional homothety formula give this identity.

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.standardSimplex_slicing_constant (n : Nat) :
    MeasureTheory.volume
        {y : Fin (n + 1) → Real | (∀ i, 0 ≤ y i) ∧ (∑ i, y i) ≤ 1} =
      ∫⁻ t in Set.Icc (0 : Real) 1,
        (ENNReal.ofReal (1 - t) ^ n *
          MeasureTheory.volume
            {y : Fin n → Real | (∀ i, 0 ≤ y i) ∧ (∑ i, y i) ≤ 1})
        ∂MeasureTheory.volume := by sorry
