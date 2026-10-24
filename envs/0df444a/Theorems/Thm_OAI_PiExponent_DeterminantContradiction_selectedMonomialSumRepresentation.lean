-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_selectedMonomialSumRepresentation
-- name    : OAI.PiExponent.DeterminantContradiction.selectedMonomialSumRepresentation
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T07:00:02.096549+00:00
-- url     : https://prove2.me/theorems/2815d3dc-1809-4cb9-96e8-c7223a9679ac
-- title:
--   Selected monomials realize matrix coefficient combinations
-- statement:
--   For any coefficients indexed by rows, a weighted polynomial supported on the selected columns has packet equal to the corresponding linear combination of columns of the actual minor. This removes the polynomial construction, weighted-support check, and packet-to-matrix identification from the parent.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.selectedMonomialSumRepresentation
    (nu : Real) (d : FixedData nu) (H : Real)
    (selection : Row d H → Column d H)
    (hinj : Function.Injective selection)
    (x : Row d H → Complex) :
    ∃ P : WeightedPolynomial d.w0 (MatrixArithmetic.logWeights (finiteDenominators d)) H,
      ∀ rho : Row d H,
        truncatedPolynomialPacket d.K d.v0 d.base.theta
          (MatrixArithmetic.logWeights (finiteDenominators d)) H
          (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
          (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0) P.1 rho =
          ∑ sigma : Row d H, (actualMinor d H selection) rho sigma * x sigma := by
  sorry
