-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weighted_floor_sum_lt
-- name    : OAI.PiExponent.DeterminantContradiction.weighted_floor_sum_lt
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T12:00:41.157408+00:00
-- url     : https://prove2.me/theorems/09087e60-6e6a-4cec-a6d9-2a9e77be3bff
-- title:
--   Weighted sum of floors remains below the cutoff
-- statement:
--   Replacing each coordinate of a nonnegative point by its natural floor preserves the strict weighted-sum cutoff. Multiply Nat.floor_le by each positive weight, sum the inequalities, and combine with the original strict bound. This also holds in dimension zero, where the sum is zero and hT supplies strictness.

import Definitions.Def_OAI_PiExponent_FixedDeterminantFamily
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.weighted_floor_sum_lt
    (n : Nat) (w : Fin n → Real) (hw : ∀ i, 0 < w i)
    (T : Real) (hT : 0 < T)
    (x : Fin n → Real)
    (hx : (∀ i, 0 ≤ x i) ∧ (∑ i, w i * x i) < T) :
    (∑ i, w i * ((Nat.floor (x i) : Nat) : Real)) < T := by sorry
