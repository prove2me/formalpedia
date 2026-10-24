-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_collisionRate_tendsto_from_counts
-- name    : OAI.PiExponent.DeterminantContradiction.collisionRate_tendsto_from_counts
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T06:19:54.569907+00:00
-- url     : https://prove2.me/theorems/7e590410-11e5-4e25-9236-e645065facba
-- title:
--   Derive the collision limit from normalized counts
-- statement:
--   Given the two normalized count limits, quotient limit algebra gives convergence of the collision rate. The low-count coefficient is positive, so the denominator is eventually nonzero; cancelling the common weight product and simplifying factorials gives `collisionLimit`. This removes the algebraic limit step from the parent. The two simplex-count children remain the core obligations.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.collisionRate_tendsto_from_counts (nu : Real) (d : FixedData nu)
    (hrow : Tendsto (fun H : Real => (actualRowCount d H : Real) / H ^ (d.m + 1)) atTop
      (nhds ((d.K : Real) * (d.base.theta : Real) ^ d.m /
        (((d.m + 1).factorial : Real) * (d.v0 : Real) *
          ∏ i : Fin d.m, MatrixArithmetic.logWeights (finiteDenominators d) i))))
    (hlow : Tendsto (fun H : Real => (lowIndexCount d H : Real) / H ^ d.m) atTop
      (nhds ((d.base.A : Real) ^ d.m /
        ((d.m.factorial : Real) *
          ∏ i : Fin d.m, MatrixArithmetic.logWeights (finiteDenominators d) i)))) :
    Tendsto (fun H : Real => collisionRate d H) atTop (nhds (collisionLimit d)) := by sorry
