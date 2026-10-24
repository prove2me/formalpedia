-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standardSimplex_sublevel_volume_scale_ennreal
-- name    : OAI.PiExponent.DeterminantContradiction.standardSimplex_sublevel_volume_scale_ennreal
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T06:56:17.141997+00:00
-- url     : https://prove2.me/theorems/3742a6ee-0e3c-4a5c-8b62-086398ac3018
-- title:
--   ENNReal scaling of a simplex sublevel volume
-- statement:
--   The ENNReal volume of the nonnegative simplex with coordinate sum at most A is A^m times the unit simplex volume. The positivity hypothesis makes scalar multiplication by A invertible and preserves the inequalities under rescaling. The case m = 0 has factor one.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.standardSimplex_sublevel_volume_scale_ennreal {m : Nat} (A : Real) (hA : 0 < A) :
    MeasureTheory.volume {x : Fin m → Real | (∀ i : Fin m, 0 ≤ x i) ∧
      ∑ i : Fin m, x i ≤ A} = ENNReal.ofReal (A ^ m) *
        MeasureTheory.volume {x : Fin m → Real | (∀ i : Fin m, 0 ≤ x i) ∧
          ∑ i : Fin m, x i ≤ 1} := by sorry
