-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_row_volume_coefficient
-- name    : OAI.PiExponent.DeterminantContradiction.row_volume_coefficient
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T23:16:23.341051+00:00
-- url     : https://prove2.me/theorems/05a3203c-875c-45ca-b0ea-71a117aa9074
-- title:
--   Simplification of the row volume coefficient
-- statement:
--   The product of the `m + 1` row weights is `v0` times the product of the remaining log weights divided by `theta^m`. The admissible data identifies those log weights with `x(i.val + 1)`, yielding the target coefficient. Positivity of `theta`, `v0`, and the x values ensures the divisions are defined with nonzero denominators.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem OAI.PiExponent.DeterminantContradiction.row_volume_coefficient
    {nu : ℝ} (d : OAI.PiExponent.DeterminantContradiction.FixedData nu) :
    (d.K : ℝ) *
        (1 / ((Nat.factorial (d.m + 1) : ℝ) *
          ∏ i : Fin (d.m + 1),
            OAI.PiExponent.InterpolationMatrix.rowWeights d.v0 d.base.theta
              (OAI.PiExponent.MatrixArithmetic.logWeights
                (OAI.PiExponent.DeterminantContradiction.finiteDenominators d)) i)) =
      ((d.K : ℝ) * (d.base.theta : ℝ) ^ d.m) /
        ((Nat.factorial (d.m + 1) : ℝ) * (d.v0 : ℝ) *
          ∏ i : Fin d.m, d.x (i.val + 1)) := by sorry
