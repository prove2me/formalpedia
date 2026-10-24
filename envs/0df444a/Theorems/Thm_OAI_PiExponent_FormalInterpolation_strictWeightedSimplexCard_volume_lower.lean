-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_strictWeightedSimplexCard_volume_lower
-- name    : OAI.PiExponent.FormalInterpolation.strictWeightedSimplexCard_volume_lower
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T04:41:08.481784+00:00
-- url     : https://prove2.me/theorems/a5e2a0bf-86ad-4302-964c-970f53546df0
-- title:
--   Volume lower bound for a strict weighted lattice simplex
-- statement:
--   Positive weights make the strict weighted lattice simplex finite. Its cardinality is at least T^r/(r! times the weight product). Prove by covering the nonnegative real simplex with unit cubes indexed by coordinatewise floors. Strictness is preserved by flooring. In dimension zero there is exactly one exponent vector and the inequality is equality.

import Definitions.Def_OAI_PiExponent_StrictWeightedSimplex
import Mathlib.Data.Nat.Factorial.Basic

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.strictWeightedSimplexCard_volume_lower
    {ι : Type*} [Fintype ι] (v : ι → Rat)
    (hv : ∀ i, 0 < (v i : Real)) (T : Real) (hT : 0 < T) :
    Finite (strictWeightedSimplex v T) ∧
      T ^ Fintype.card ι ≤
        ((Fintype.card ι).factorial : Real) * (∏ i, (v i : Real)) *
          (strictWeightedSimplexCard v T : Real) := by
  sorry
