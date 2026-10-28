-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_strictWeightedSimplexCard_volume_lower_v2
-- name    : OAI.PiExponent.FormalInterpolation.strictWeightedSimplexCard_volume_lower_v2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T08:47:54.877382+00:00
-- url     : https://prove2.me/theorems/64d74a7f-f0ba-4f0c-8e78-1aa33eea2ac9
-- title:
--   Volume lower bound for a strict weighted lattice simplex
-- statement:
--   This isolates the numerical volume estimate for positive weights and positive cutoff. Finiteness follows by bounding each coordinate of a counted exponent vector using its positive weight. For the inequality, floor each point of the nonnegative real simplex coordinatewise: positivity ensures the resulting integer vector has weight strictly below `T`. The unit boxes indexed by these vectors cover the simplex, giving the factorial volume bound. In dimension zero the inequality is equality. This removes the lattice-volume estimate from the parent.

import Definitions.Def_OAI_PiExponent_StrictWeightedSimplex
import Mathlib.Data.Nat.Factorial.Basic

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.strictWeightedSimplexCard_volume_lower_v2
    {ι : Type*} [Fintype ι] (v : ι → Rat)
    (hv : ∀ i, 0 < (v i : Real)) (T : Real) (hT : 0 < T) :
    Finite (strictWeightedSimplex v T) ∧
      T ^ Fintype.card ι ≤
        ((Fintype.card ι).factorial : Real) * (∏ i, (v i : Real)) *
          (strictWeightedSimplexCard v T : Real) := by
  sorry
