-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_actual_packet_canonical_coefficients
-- name    : OAI.PiExponent.DeterminantContradiction.actual_packet_canonical_coefficients
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T06:13:54.576849+00:00
-- url     : https://prove2.me/theorems/185909d0-1969-44d3-a581-febb033abf0c
-- title:
--   The actual packet equals its canonical matrix coefficient vector
-- statement:
--   For positive column weights, the packet of a supported polynomial is the actual interpolation matrix applied to its monomial coefficient vector.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.actual_packet_canonical_coefficients
    (nu : Real) (d : FixedData nu) (H : Real)
    (hw0 : 0 < (d.w0 : Real))
    (hw : ∀ i : Fin d.m,
      0 < MatrixArithmetic.logWeights (finiteDenominators d) i)
    (P : WeightedPolynomial d.w0
      (MatrixArithmetic.logWeights (finiteDenominators d)) H) :
    truncatedPolynomialPacket d.K d.v0 d.base.theta
      (MatrixArithmetic.logWeights (finiteDenominators d)) H
      (MatrixArithmetic.rationalCenters (finiteNumerators d)
        (finiteDenominators d))
      (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)
      P.val =
    (actualMatrix d H).mulVecLin
      (fun c : Column d H =>
        P.val.coeff (InterpolationMatrix.exponentVector c.1)) := by sorry
