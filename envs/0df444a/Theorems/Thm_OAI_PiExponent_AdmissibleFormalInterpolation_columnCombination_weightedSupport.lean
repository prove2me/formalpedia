-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_columnCombination_weightedSupport
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.columnCombination_weightedSupport
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T12:47:46.086983+00:00
-- url     : https://prove2.me/theorems/95e1dde6-202e-4921-a069-862ac1734c56
-- title:
--   Column combinations preserve the weighted support bound
-- statement:
--   Every exponent in the finite column combination satisfies the weighted support bound. Each summand is a monomial at a column exponent that already satisfies the bound; zero coefficients and the empty column set are covered.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_ColumnCombination

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.columnCombination_weightedSupport
    {m : ℕ} (w0 : ℝ) (w : Fin m → ℝ) (H : ℝ)
    (x : InterpolationMatrix.Column w0 w H → ℂ) :
    ∀ a ∈ (columnCombination w0 w H x).support,
      ∑ i, InterpolationMatrix.columnWeights w0 w i * (a i : ℝ) ≤ H := by sorry
