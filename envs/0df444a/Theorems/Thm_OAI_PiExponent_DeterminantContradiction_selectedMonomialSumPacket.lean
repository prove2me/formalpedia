-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_selectedMonomialSumPacket
-- name    : OAI.PiExponent.DeterminantContradiction.selectedMonomialSumPacket
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T07:12:15.657399+00:00
-- url     : https://prove2.me/theorems/9d480601-1822-458f-9bb3-306dc485b466
-- title:
--   The selected monomial sum has the matrix combination packet
-- statement:
--   At every row index, the truncated polynomial packet of the selected monomial sum equals the corresponding linear combination of entries of the selected minor.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.selectedMonomialSumPacket
    (nu : Real) (d : FixedData nu) (H : Real)
    (selection : Row d H → Column d H)
    (x : Row d H → Complex) :
    ∀ rho : Row d H,
      truncatedPolynomialPacket d.K d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) H
        (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
        (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)
        (∑ sigma : Row d H,
          MvPolynomial.C (x sigma) *
            MvPolynomial.monomial
              (InterpolationMatrix.exponentVector (selection sigma).1) 1) rho =
      ∑ sigma : Row d H, (actualMinor d H selection) rho sigma * x sigma := by
  sorry
