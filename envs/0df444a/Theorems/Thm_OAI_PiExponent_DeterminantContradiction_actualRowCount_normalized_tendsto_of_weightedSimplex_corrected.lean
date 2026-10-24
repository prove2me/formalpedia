-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_actualRowCount_normalized_tendsto_of_weightedSimplex_corrected
-- name    : OAI.PiExponent.DeterminantContradiction.actualRowCount_normalized_tendsto_of_weightedSimplex_corrected
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T06:30:34.146183+00:00
-- url     : https://prove2.me/theorems/1d75d58f-9d8d-48ea-9bf1-6b9d54d187ab
-- title:
--   Transfer the weighted-simplex limit to actual rows
-- statement:
--   Given the normalized limit for the strict simplex with the fixed-data row weights, derive the normalized limit for `actualRowCount`. The row type contributes `d.K` copies. Expanding the product of row weights yields the stated coefficient. This isolates the finite-cardinality and algebraic bridge from the lattice-count estimate.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.actualRowCount_normalized_tendsto_of_weightedSimplex_corrected
    (nu : Real) (d : FixedData nu)
    (h : Tendsto
      (fun H : Real =>
        ((strictWeightedSimplex
          (InterpolationMatrix.rowWeights d.v0 d.base.theta
            (MatrixArithmetic.logWeights (finiteDenominators d))) H).card : Real) /
          H ^ (d.m + 1)) atTop
      (nhds (1 /
        (((d.m + 1).factorial : Real) *
          ∏ i : Fin (d.m + 1),
            InterpolationMatrix.rowWeights d.v0 d.base.theta
              (MatrixArithmetic.logWeights (finiteDenominators d)) i)))) :
    Tendsto (fun H : Real => (actualRowCount d H : Real) / H ^ (d.m + 1)) atTop
      (nhds ((d.K : Real) * (d.base.theta : Real) ^ d.m /
        (((d.m + 1).factorial : Real) * (d.v0 : Real) *
          ∏ i : Fin d.m, MatrixArithmetic.logWeights (finiteDenominators d) i))) := by sorry
