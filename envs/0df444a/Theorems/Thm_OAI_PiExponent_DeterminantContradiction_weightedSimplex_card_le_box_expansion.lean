-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplex_card_le_box_expansion
-- name    : OAI.PiExponent.DeterminantContradiction.weightedSimplex_card_le_box_expansion
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T09:55:12.294934+00:00
-- url     : https://prove2.me/theorems/61f293b8-28b9-4598-81ca-fb3edf40445e
-- title:
--   Lattice count bounded by the volume of the expanded weighted simplex
-- statement:
--   For positive coordinate weights and nonnegative height, the number of lattice points with weighted sum strictly below the height is at most the volume of the weighted simplex expanded by one unit in every coordinate.

import Definitions.Def_OAI_PiExponent_FixedDeterminantFamily
import Mathlib.Data.Real.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.weightedSimplex_card_le_box_expansion
    (n : Nat) (w : Fin n → Real) (hw : ∀ i, 0 < w i) (H : Real) (hH : 0 ≤ H) :
    ((strictWeightedSimplex w H).card : Real) ≤
      (H + Finset.univ.sum w) ^ n /
        ((n.factorial : Real) * Finset.univ.prod w) := by sorry
