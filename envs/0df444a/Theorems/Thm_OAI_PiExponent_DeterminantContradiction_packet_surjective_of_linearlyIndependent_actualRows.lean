-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_packet_surjective_of_linearlyIndependent_actualRows
-- name    : OAI.PiExponent.DeterminantContradiction.packet_surjective_of_linearlyIndependent_actualRows
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T07:14:15.891485+00:00
-- url     : https://prove2.me/theorems/e43f5331-6e56-4993-a278-7e8bb3b8e6ca
-- title:
--   Independent actual rows give packet surjectivity
-- statement:
--   At a fixed height, linear independence of the actual matrix rows makes the finite-dimensional coefficient-to-row map surjective. For any desired row values, choose coefficients on the weak-cutoff columns and form the polynomial supported on those monomials. The coefficient identity between each monomial’s truncated packet and the corresponding actual-matrix entry gives the requested packet. This removes the algebraic and support bookkeeping from the parent; the independent-row hypothesis supplies the rank, and the weak support cutoff matches the polynomial domain exactly.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.packet_surjective_of_linearlyIndependent_actualRows
    (nu : Real) (d : FixedData nu) (H : Real)
    (hrows : LinearIndependent ℂ (fun ρ : Row d H => actualMatrix d H ρ)) :
    Function.Surjective
      (fun P : WeightedPolynomial d.w0 (MatrixArithmetic.logWeights (finiteDenominators d)) H =>
        truncatedPolynomialPacket d.K d.v0 d.base.theta
          (MatrixArithmetic.logWeights (finiteDenominators d)) H
          (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
          (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0) P.1) := by sorry
