-- Prove2me | Theorems.Thm_OAI_PiExponent_MatrixArithmetic_det_of_rowwise_Gaussian_denominators
-- name    : OAI.PiExponent.MatrixArithmetic.det_of_rowwise_Gaussian_denominators
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T22:56:12.044358+00:00
-- url     : https://prove2.me/theorems/61818701-9547-4b92-87fb-81f87c55a2e7
-- title:
--   Determinant denominator from rowwise Gaussian scales
-- statement:
--   If each row of a finite square complex matrix becomes Gaussian-integral after multiplication by a positive integer, then a product of those integers clears the determinant denominator, with logarithmic cost at most the sum of the row costs.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData

open scoped BigOperators

theorem OAI.PiExponent.MatrixArithmetic.det_of_rowwise_Gaussian_denominators
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (d : ι → ℕ) (b : ι → ℝ)
    (hd : ∀ i, 0 < d i)
    (hentry : ∀ i j, ∃ g : GaussianInt, (d i : ℂ) * M i j = (g : ℂ))
    (hlog : ∀ i, Real.log (d i : ℝ) ≤ b i) :
    ∃ D : ℕ, 0 < D ∧
      ∃ g : GaussianInt, (D : ℂ) * M.det = (g : ℂ) ∧
        Real.log (D : ℝ) ≤ ∑ i, b i := by sorry
