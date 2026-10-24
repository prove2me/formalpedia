-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplex_card_lower_eventually
-- name    : OAI.PiExponent.DeterminantContradiction.weightedSimplex_card_lower_eventually
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T09:50:05.103744+00:00
-- url     : https://prove2.me/theorems/f487809d-a247-42b3-97a3-9a22655a9998
-- title:
--   Lower bound for the strict weighted simplex count
-- statement:
--   Eventually, the strict weighted-simplex lattice count is at least the volume of the nonnegative simplex whose height is reduced by the sum of the weights.

import Definitions.Def_OAI_PiExponent_FixedDeterminantFamily
import Mathlib.Data.Real.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.weightedSimplex_card_lower_eventually
    (n : Nat) (w : Fin n → Real) (hw : ∀ i, 0 < w i) :
    Filter.Eventually
      (fun H : Real =>
        (H - Finset.univ.sum w) ^ n /
          ((n.factorial : Real) * Finset.univ.prod w)
          ≤ ((strictWeightedSimplex w H).card : Real))
      atTop := by sorry
