-- Prove2me | Theorems.Thm_OAI_PiExponent_MatrixArithmetic_selectedMinor_row_denominator_bound
-- name    : OAI.PiExponent.MatrixArithmetic.selectedMinor_row_denominator_bound
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-16T22:38:41.769435+00:00
-- url     : https://prove2.me/theorems/34d186d7-479e-4ce4-ac83-4b5c9205a2cc
-- title:
--   Rowwise denominator bound for selected-minor entries
-- statement:
--   For each row of the selected minor, find a positive integer that clears the Gaussian denominators of every entry in that row, with logarithmic cost bounded by the row's unused weighted degree budget and the stated arithmetic terms.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData

open scoped BigOperators

theorem OAI.PiExponent.MatrixArithmetic.selectedMinor_row_denominator_bound
    {m K : ℕ} {w0 v0 θ F H wmin : ℝ}
    (p : Fin m → ℤ) (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i)
    (hK : 0 < K) (hw0 : 0 < w0) (hv0 : 0 < v0) (hθ : 0 < θ)
    (hF : 0 ≤ F) (hH : 0 < H) (hmin : 0 < wmin)
    (hwmin : ∀ i, wmin ≤ OAI.PiExponent.MatrixArithmetic.logWeights q i)
    (selection : OAI.PiExponent.InterpolationMatrix.Row K v0 θ
        (OAI.PiExponent.MatrixArithmetic.logWeights q) H →
      OAI.PiExponent.InterpolationMatrix.Column w0
        (OAI.PiExponent.MatrixArithmetic.logWeights q) H) :
    ∃ d : OAI.PiExponent.InterpolationMatrix.Row K v0 θ
        (OAI.PiExponent.MatrixArithmetic.logWeights q) H → ℕ,
      (∀ ρ, 0 < d ρ) ∧
      (∀ ρ c, ∃ g : GaussianInt,
        (d ρ : ℂ) *
          OAI.PiExponent.MatrixArithmetic.selectedMinor K w0 v0 θ F H p q selection ρ c = (g : ℂ)) ∧
      (∀ ρ, Real.log (d ρ : ℝ) ≤
        H - (∑ i, (ρ.2.1 i.succ : ℝ) * OAI.PiExponent.MatrixArithmetic.logWeights q i) +
          H * (OAI.PiExponent.Arithmetic.lcmConstant * F * m / v0 +
            OAI.PiExponent.Arithmetic.lcmConstant *
              (∑ i, 1 / OAI.PiExponent.MatrixArithmetic.logWeights q i) + θ / wmin)) := by sorry
