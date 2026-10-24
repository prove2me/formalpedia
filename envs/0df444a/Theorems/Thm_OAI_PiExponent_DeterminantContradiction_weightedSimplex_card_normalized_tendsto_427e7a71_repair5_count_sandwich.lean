-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplex_card_normalized_tendsto_427e7a71_repair5_count_sandwich
-- name    : OAI.PiExponent.DeterminantContradiction.weightedSimplex_card_normalized_tendsto_427e7a71_repair5_count_sandwich
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T08:32:10.099749+00:00
-- url     : https://prove2.me/theorems/a0c01178-e0b1-447a-bc3d-607b7903df13
-- title:
--   Weighted simplex count bounded by shifted volumes
-- statement:
--   Eventually, the number of strict weighted-simplex lattice points lies between the volumes of simplices whose heights are shifted down and up by the sum of the weights. The lower bound follows by flooring coordinates; the upper bound follows from disjoint unit cells.

import Definitions.Def_OAI_PiExponent_FixedDeterminantFamily
import Mathlib.Data.Real.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.weightedSimplex_card_normalized_tendsto_427e7a71_repair5_count_sandwich
    (n : Nat) (w : Fin n → Real) (hw : ∀ i, 0 < w i) :
    Filter.Eventually
      (fun H : Real => And
        ((H - Finset.univ.sum w) ^ n /
          ((n.factorial : Real) * Finset.univ.prod w)
          ≤ ((strictWeightedSimplex w H).card : Real))
        (((strictWeightedSimplex w H).card : Real) ≤
          (H + Finset.univ.sum w) ^ n /
            ((n.factorial : Real) * Finset.univ.prod w)))
      atTop := by sorry
