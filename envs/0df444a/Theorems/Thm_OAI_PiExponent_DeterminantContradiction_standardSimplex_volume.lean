-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standardSimplex_volume
-- name    : OAI.PiExponent.DeterminantContradiction.standardSimplex_volume
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T10:13:49.610984+00:00
-- url     : https://prove2.me/theorems/f4d0dce0-178b-4b1e-8607-2083795f42ff
-- title:
--   Volume of the standard closed simplex
-- statement:
--   The standard closed simplex in Fin n-dimensional real space has volume 1/n!, including dimension zero. A proof route is induction on n using simplex slices and the integral formula for volume.

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.standardSimplex_volume (n : Nat) :
    MeasureTheory.volume
        {y : Fin n → Real | (∀ i, 0 ≤ y i) ∧ (∑ i, y i) ≤ 1} =
      ENNReal.ofReal (1 / (n.factorial : Real)) := by sorry
