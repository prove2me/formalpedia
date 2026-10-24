-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplex_card_normalized_tendsto_427e7a71_bounds_tendsto
-- name    : OAI.PiExponent.DeterminantContradiction.weightedSimplex_card_normalized_tendsto_427e7a71_bounds_tendsto
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T06:40:01.033881+00:00
-- url     : https://prove2.me/theorems/a9e52943-6549-4561-99fc-806ecd04e7b2
-- title:
--   Normalized shifted simplex volumes have the same limit
-- statement:
--   Both shifted volume bounds, normalized by H^n, converge to the reciprocal of n! times the product of the weights. Factor out H^n and use the limit of the resulting shifted powers; positivity of the weights gives a nonzero denominator, including the empty-product case n = 0.

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Instances.Real.Lemmas
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.weightedSimplex_card_normalized_tendsto_427e7a71_bounds_tendsto
    (n : Nat) (w : Fin n -> Real) (hw : forall i, 0 < w i) :
    And
      (Tendsto (fun H : Real =>
        (H - Finset.univ.sum w) ^ n / ((n.factorial : Real) * Finset.univ.prod w) / H ^ n)
        atTop (nhds (1 / ((n.factorial : Real) * Finset.univ.prod w))))
      (Tendsto (fun H : Real =>
        (H + Finset.univ.sum w) ^ n / ((n.factorial : Real) * Finset.univ.prod w) / H ^ n)
        atTop (nhds (1 / ((n.factorial : Real) * Finset.univ.prod w)))) := by sorry
