-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_packet_surjective_of_nonzero_actualMinor
-- name    : OAI.PiExponent.DeterminantContradiction.packet_surjective_of_nonzero_actualMinor
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T06:56:42.690677+00:00
-- url     : https://prove2.me/theorems/2188bd56-ef1d-4510-a6f0-18e7cd03ddef
-- title:
--   A nonzero interpolation minor realizes every packet
-- statement:
--   Given an injective selection of columns with nonzero determinant on all rows, the truncated polynomial packet map is surjective. For each desired packet, solve the selected square linear system and form the polynomial using only the selected monomials. Injectivity keeps their coefficients distinct, and each selected column lies in the weak weighted simplex, so the polynomial belongs to the required weighted domain. This is an algebraic bridge from the determinant witness to the parent target; it can be proved by identifying packet evaluation on monomials with the entries of the bundled truncated-log matrix and applying finite-dimensional linear algebra.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.packet_surjective_of_nonzero_actualMinor
    (nu : Real) (d : FixedData nu) (H : Real)
    (selection : Row d H → Column d H)
    (hinj : Function.Injective selection)
    (hdet : (actualMinor d H selection).det ≠ 0) :
    Function.Surjective
      (fun P : WeightedPolynomial d.w0 (MatrixArithmetic.logWeights (finiteDenominators d)) H =>
        truncatedPolynomialPacket d.K d.v0 d.base.theta
          (MatrixArithmetic.logWeights (finiteDenominators d)) H
          (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
          (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0) P.1) := by sorry
