-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplex_card_normalized_tendsto_427e7a71_repair5_bounds_tendsto
-- name    : OAI.PiExponent.DeterminantContradiction.weightedSimplex_card_normalized_tendsto_427e7a71_repair5_bounds_tendsto
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T08:32:33.796628+00:00
-- url     : https://prove2.me/theorems/c7d2560b-d2db-4ca7-a48f-9e6555f1ac48
-- title:
--   Normalized shifted volumes converge
-- statement:
--   Both shifted simplex volumes, after normalization by H^n, converge to the reciprocal of n! times the product of the weights. Positivity makes this denominator nonzero, including the empty-product case.

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Instances.Real.Lemmas
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.weightedSimplex_card_normalized_tendsto_427e7a71_repair5_bounds_tendsto
    (n : Nat) (w : Fin n → Real) (hw : ∀ i, 0 < w i) :
    And
      (Tendsto (fun H : Real =>
        ((H - Finset.univ.sum w) ^ n /
          ((n.factorial : Real) * Finset.univ.prod w)) / H ^ n)
        atTop (nhds (1 / ((n.factorial : Real) * Finset.univ.prod w))))
      (Tendsto (fun H : Real =>
        ((H + Finset.univ.sum w) ^ n /
          ((n.factorial : Real) * Finset.univ.prod w)) / H ^ n)
        atTop (nhds (1 / ((n.factorial : Real) * Finset.univ.prod w)))) := by sorry
