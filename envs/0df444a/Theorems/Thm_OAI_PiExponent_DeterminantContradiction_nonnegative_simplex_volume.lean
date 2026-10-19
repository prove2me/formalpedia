-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_nonnegative_simplex_volume
-- name    : OAI.PiExponent.DeterminantContradiction.nonnegative_simplex_volume
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T02:56:36.335348+00:00
-- url     : https://prove2.me/theorems/a8fecd2a-ff21-4171-a801-4f85f671f092
-- title:
--   Volume of a nonnegative simplex
-- statement:
--   The volume of the nonnegative simplex in $m$ real coordinates with coordinate sum at most $U$ is $U^m/m!$ for every nonnegative cutoff, including $m=0$ and $U=0$.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib

open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.nonnegative_simplex_volume
    (m : ℕ) (U : ℝ) (hU : 0 ≤ U) :
    (MeasureTheory.volume
      {x : Fin m → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, x i ≤ U}).toReal =
      U ^ m / (Nat.factorial m : ℝ) := by sorry
