-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplex_card_normalized_tendsto_427e7a71_repair6_count_sandwich
-- name    : OAI.PiExponent.DeterminantContradiction.weightedSimplex_card_normalized_tendsto_427e7a71_repair6_count_sandwich
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T09:43:52.086897+00:00
-- url     : https://prove2.me/theorems/dd266a6d-2897-4b62-8cf8-05690cb81eff
-- title:
--   Weighted simplex count bounded by shifted volumes
-- statement:
--   Eventually, the strict weighted-simplex lattice count lies between the volumes of simplices with heights shifted down and up by the sum of the weights. Disjoint unit cubes give the upper bound; flooring coordinates gives the lower bound. For n = 0 both bounds reduce to the unique empty tuple and value 1.

import Definitions.Def_OAI_PiExponent_FixedDeterminantFamily
import Mathlib.Data.Real.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.weightedSimplex_card_normalized_tendsto_427e7a71_repair6_count_sandwich
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
