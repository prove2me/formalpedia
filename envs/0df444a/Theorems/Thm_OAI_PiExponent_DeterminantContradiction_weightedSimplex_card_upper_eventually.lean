-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplex_card_upper_eventually
-- name    : OAI.PiExponent.DeterminantContradiction.weightedSimplex_card_upper_eventually
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T09:50:24.435795+00:00
-- url     : https://prove2.me/theorems/2eab401e-00e3-4903-af4c-b263018a4cba
-- title:
--   Upper bound for the strict weighted simplex count
-- statement:
--   Eventually, the strict weighted-simplex lattice count is at most the volume of the nonnegative simplex whose height is increased by the sum of the weights.

import Definitions.Def_OAI_PiExponent_FixedDeterminantFamily
import Mathlib.Data.Real.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.weightedSimplex_card_upper_eventually
    (n : Nat) (w : Fin n → Real) (hw : ∀ i, 0 < w i) :
    Filter.Eventually
      (fun H : Real =>
        ((strictWeightedSimplex w H).card : Real) ≤
          (H + Finset.univ.sum w) ^ n /
            ((n.factorial : Real) * Finset.univ.prod w))
      atTop := by sorry
