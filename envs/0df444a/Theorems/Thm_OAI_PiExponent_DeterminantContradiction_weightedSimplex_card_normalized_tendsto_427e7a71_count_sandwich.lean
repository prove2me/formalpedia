-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplex_card_normalized_tendsto_427e7a71_count_sandwich
-- name    : OAI.PiExponent.DeterminantContradiction.weightedSimplex_card_normalized_tendsto_427e7a71_count_sandwich
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T06:39:48.101979+00:00
-- url     : https://prove2.me/theorems/05dcede0-3a79-42da-9972-b1ed6daf94ff
-- title:
--   Weighted simplex count lies between shifted simplex volumes
-- statement:
--   Eventually, the strict weighted-simplex lattice count is bounded by the volumes of simplices with heights shifted down and up by the sum of the weights. Disjoint unit boxes give the upper bound; flooring coordinates gives the lower bound.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.weightedSimplex_card_normalized_tendsto_427e7a71_count_sandwich
    (n : Nat) (w : Fin n -> Real) (hw : forall i, 0 < w i) :
    Filter.Eventually
      (fun H : Real => And
        ((H - Finset.univ.sum w) ^ n / ((n.factorial : Real) * Finset.univ.prod w)
          <= ((strictWeightedSimplex w H).card : Real))
        (((strictWeightedSimplex w H).card : Real) <=
          (H + Finset.univ.sum w) ^ n / ((n.factorial : Real) * Finset.univ.prod w)))
      atTop := by sorry
