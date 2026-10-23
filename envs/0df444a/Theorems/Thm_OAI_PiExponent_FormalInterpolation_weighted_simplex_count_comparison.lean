-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_simplex_count_comparison
-- name    : OAI.PiExponent.FormalInterpolation.weighted_simplex_count_comparison
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-21T13:45:22.29064+00:00
-- url     : https://prove2.me/theorems/c3126117-157e-4455-85b9-5795c371f279
-- title:
--   Strict volume gives an eventual weighted simplex count comparison
-- statement:
--   For positive rational coordinate weights, the strict volume inequality guarantees that for every sufficiently large natural N, the number of polynomial exponent vectors of W-weight at most N exceeds K times the number of exponent vectors of V-weight strictly below aN. Both exponent regions are finite.
-- source:
--   openai/math Approximation FibreNormalRigidity: nonconstant fibre coordinates imply quantitative contact bound.

import Definitions.Def_OAI_PiExponent_FibreContactAuxiliaryData
import Mathlib.Data.Set.Card

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.weighted_simplex_count_comparison
    (n K : Nat) (W V : Fin n → Rat)
    (hW : ∀ i, 0 < (W i : Real)) (hV : ∀ i, 0 < (V i : Real))
    (a : Real) (ha : 0 < a)
    (hvolume : (K : Real) * a ^ n *
      (∏ i : Fin n, (W i : Real)) / (∏ i : Fin n, (V i : Real)) < 1) :
    ∃ N0 : Nat, ∀ N : Nat, N0 ≤ N →
      Set.Finite {m : Fin n →₀ Nat |
        (∑ i : Fin n, (m i : Real) * (W i : Real)) ≤ (N : Real)} ∧
      Set.Finite {b : Fin n →₀ Nat |
        (∑ i : Fin n, (b i : Real) * (V i : Real)) < a * (N : Real)} ∧
      Set.ncard {m : Fin n →₀ Nat |
        (∑ i : Fin n, (m i : Real) * (W i : Real)) ≤ (N : Real)} >
        K * Set.ncard {b : Fin n →₀ Nat |
        (∑ i : Fin n, (b i : Real) * (V i : Real)) < a * (N : Real)} := by sorry
