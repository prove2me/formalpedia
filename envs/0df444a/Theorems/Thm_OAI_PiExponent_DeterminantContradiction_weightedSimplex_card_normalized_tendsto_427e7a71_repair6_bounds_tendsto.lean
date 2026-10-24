-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplex_card_normalized_tendsto_427e7a71_repair6_bounds_tendsto
-- name    : OAI.PiExponent.DeterminantContradiction.weightedSimplex_card_normalized_tendsto_427e7a71_repair6_bounds_tendsto
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T09:44:07.889835+00:00
-- url     : https://prove2.me/theorems/e3748254-284b-4077-af96-5316624540bf
-- title:
--   Normalized shifted volumes converge
-- statement:
--   Both shifted simplex volumes, normalized by Hⁿ, converge to 1/(n! ∏ wᵢ). Positivity makes the denominator nonzero; for n = 0 the normalized expressions are constant.

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Instances.Real.Lemmas
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.weightedSimplex_card_normalized_tendsto_427e7a71_repair6_bounds_tendsto
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
