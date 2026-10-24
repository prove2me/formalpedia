-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_actualRowCount_normalized_tendsto
-- name    : OAI.PiExponent.DeterminantContradiction.actualRowCount_normalized_tendsto
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T06:20:13.671546+00:00
-- url     : https://prove2.me/theorems/e9d7243d-947d-41b8-a498-69fafafcd424
-- title:
--   Asymptotic count of strict weighted rows
-- statement:
--   For each admissible datum, the number of strict weighted rows, divided by `H^(m+1)`, tends to the volume coefficient of the row simplex times its `K` copies. FixedData gives positive row weights; the strict boundary affects only a lower-order count. This removes the row-count asymptotic from the parent. A proof route is to scale the simplex by `1/H`, cover it with grid boxes, and bound the discrepancy by boxes meeting its boundary. The weighted lattice-point estimate remains substantive work.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.actualRowCount_normalized_tendsto (nu : Real) (d : FixedData nu) :
    Tendsto (fun H : Real => (actualRowCount d H : Real) / H ^ (d.m + 1)) atTop
      (nhds ((d.K : Real) * (d.base.theta : Real) ^ d.m /
        (((d.m + 1).factorial : Real) * (d.v0 : Real) *
          ∏ i : Fin d.m, MatrixArithmetic.logWeights (finiteDenominators d) i))) := by sorry
