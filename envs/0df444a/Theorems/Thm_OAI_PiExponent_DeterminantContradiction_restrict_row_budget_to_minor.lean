-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_restrict_row_budget_to_minor
-- name    : OAI.PiExponent.DeterminantContradiction.restrict_row_budget_to_minor
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T09:21:09.516725+00:00
-- url     : https://prove2.me/theorems/ad4c0999-6995-4bcb-9a08-40382d12385d
-- title:
--   Restrict a full-row denominator budget to a selected minor
-- statement:
--   Given a positive scale for each row that clears every full-matrix entry within the stated logarithmic budget, use the same scales to clear the selected-minor entries and retain the budget.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.restrict_row_budget_to_minor
    {nu : Real} (d : FixedData nu) (H : Real) (hH : 0 < H)
    (selection : Row d H → Column d H)
    (hfull : ∃ scale : Row d H → Nat,
      (∀ ρ, 0 < scale ρ) ∧
      (∀ ρ c, ∃ a b : Int,
        (scale ρ : Complex) * (actualMatrix d H) ρ c =
          (a : Complex) + Complex.I * (b : Complex)) ∧
      (∀ ρ : Row d H,
        Real.log (scale ρ : Real) ≤
          H - (∑ i : Fin d.m, (ρ.2.1 i.succ : Real) *
            MatrixArithmetic.logWeights (finiteDenominators d) i) +
            H * d.arithmeticError)) :
    ∃ scale : Row d H → Nat,
      (∀ ρ, 0 < scale ρ) ∧
      (∀ ρ σ, ∃ a b : Int,
        (scale ρ : Complex) * (actualMinor d H selection) ρ σ =
          (a : Complex) + Complex.I * (b : Complex)) ∧
      (∀ ρ : Row d H,
        Real.log (scale ρ : Real) ≤
          H - (∑ i : Fin d.m, (ρ.2.1 i.succ : Real) *
            MatrixArithmetic.logWeights (finiteDenominators d) i) +
            H * d.arithmeticError) := by sorry
