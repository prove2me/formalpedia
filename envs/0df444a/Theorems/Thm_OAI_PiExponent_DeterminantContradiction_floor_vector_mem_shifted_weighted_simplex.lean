-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_floor_vector_mem_shifted_weighted_simplex
-- name    : OAI.PiExponent.DeterminantContradiction.floor_vector_mem_shifted_weighted_simplex
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T12:00:25.221451+00:00
-- url     : https://prove2.me/theorems/064886dc-a8f8-4fb6-a658-ed4383e584fd
-- title:
--   Floor vector belongs to the shifted weighted simplex
-- statement:
--   The coordinatewise natural floors of a nonnegative point in the weighted simplex belong to the finite shifted weighted simplex. The shifted cutoff must accommodate both the weighted bound and the coordinatewise range used in realWeightedSimplex. For n = 0 the range conditions are vacuous. A proof route is to use positivity of each weight and nonnegativity of all summands to bound x i by the weighted-sum cutoff, then use the added sum of weights to show each floor lies below the defining natural range; floor ≤ x gives the weighted bound.

import Definitions.Def_OAI_PiExponent_FixedDeterminantFamily
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.floor_vector_mem_shifted_weighted_simplex
    (n : Nat) (w : Fin n → Real) (hw : ∀ i, 0 < w i)
    (T : Real) (hT : 0 < T)
    (x : Fin n → Real)
    (hx : (∀ i, 0 ≤ x i) ∧ (∑ i, w i * x i) < T) :
    (fun i => Nat.floor (x i)) ∈ realWeightedSimplex w (T + Finset.univ.sum w) := by sorry
