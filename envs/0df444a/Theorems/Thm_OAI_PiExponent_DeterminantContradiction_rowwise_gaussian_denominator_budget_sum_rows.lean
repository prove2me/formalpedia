-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_rowwise_gaussian_denominator_budget_sum_rows
-- name    : OAI.PiExponent.DeterminantContradiction.rowwise_gaussian_denominator_budget_sum_rows
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T09:14:14.841538+00:00
-- url     : https://prove2.me/theorems/5fcc62f6-2bb6-40fa-bcac-25ba72138285
-- title:
--   Aggregate row-wise logarithmic denominator budgets
-- statement:
--   Sum per-row log-scale bounds over the finite row type and rewrite the total weighted row degree as `actualRowCount * H * actualMean`; positivity of H is part of the hypotheses for this aggregation.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.rowwise_gaussian_denominator_budget_sum_rows
    {nu : Real} (d : FixedData nu) (H : Real) (hH : 0 < H)
    (scale : Row d H → Nat)
    (hrow : ∀ ρ : Row d H,
      Real.log (scale ρ : Real) ≤
        H - (∑ i : Fin d.m, (ρ.2.1 i.succ : Real) *
          MatrixArithmetic.logWeights (finiteDenominators d) i) +
          H * d.arithmeticError) :
    (∑ ρ : Row d H, Real.log (scale ρ : Real)) ≤
      ((actualRowCount d H : Real) * H) *
        (1 - actualMean d H + d.arithmeticError) := by sorry
