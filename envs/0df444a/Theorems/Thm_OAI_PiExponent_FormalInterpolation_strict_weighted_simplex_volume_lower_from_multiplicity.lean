-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_strict_weighted_simplex_volume_lower_from_multiplicity
-- name    : OAI.PiExponent.FormalInterpolation.strict_weighted_simplex_volume_lower_from_multiplicity
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T20:37:14.374176+00:00
-- url     : https://prove2.me/theorems/50c00270-cf10-4871-a749-8c962498335d
-- title:
--   Volume lower bound for the strict weighted simplex
-- statement:
--   Positive weights make the strict weighted simplex finite. Flooring points of the nonnegative real simplex gives a cover indexed by integer exponent vectors whose weight remains strictly below T, yielding the stated volume bound. The zero-dimensional case is equality. This removes the numerical counting step from the parent.

import Definitions.Def_OAI_PiExponent_StrictWeightedSimplex
import Mathlib.Data.Nat.Factorial.Basic

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.strict_weighted_simplex_volume_lower_from_multiplicity
    {ι : Type*} [Fintype ι] (v : ι → Rat)
    (hv : ∀ i, 0 < (v i : Real)) (T : Real) (hT : 0 < T) :
    Finite (strictWeightedSimplex v T) ∧
      T ^ Fintype.card ι ≤
        ((Fintype.card ι).factorial : Real) *
          (∏ i, (v i : Real)) * (strictWeightedSimplexCard v T : Real) := by
  sorry
