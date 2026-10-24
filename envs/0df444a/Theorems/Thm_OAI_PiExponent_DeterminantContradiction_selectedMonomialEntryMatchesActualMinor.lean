-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_selectedMonomialEntryMatchesActualMinor
-- name    : OAI.PiExponent.DeterminantContradiction.selectedMonomialEntryMatchesActualMinor
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T16:50:57.065003+00:00
-- url     : https://prove2.me/theorems/fc96b802-d739-41b5-9eea-b0c4cf70d563
-- title:
--   A selected monomial coefficient is the corresponding actual minor entry
-- statement:
--   For each row and selected column, the coefficient of the substituted selected monomial equals the corresponding entry of the actual minor. This isolates the coefficient-to-matrix-entry calculation used by the parent sum identity.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.selectedMonomialEntryMatchesActualMinor
    (nu : Real) (d : FixedData nu) (H : Real)
    (selection : Row d H → Column d H)
    (rho sigma : Row d H) :
    (truncatedPolynomialJet
      (fun i => (rho.1.val : Complex) *
        MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i)
      (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)
      (MvPolynomial.monomial
        (InterpolationMatrix.exponentVector (selection sigma).1) 1)).coeff
      (InterpolationMatrix.exponentVector rho.2.1) =
      (actualMinor d H selection) rho sigma := by sorry
