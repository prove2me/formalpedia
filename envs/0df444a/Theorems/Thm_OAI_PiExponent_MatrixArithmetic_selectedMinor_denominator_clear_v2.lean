-- Prove2me | Theorems.Thm_OAI_PiExponent_MatrixArithmetic_selectedMinor_denominator_clear_v2
-- name    : OAI.PiExponent.MatrixArithmetic.selectedMinor_denominator_clear_v2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T22:21:35.863323+00:00
-- url     : https://prove2.me/theorems/2df08a8d-4ce4-4add-9afe-541d9fbfc388
-- title:
--   Arithmetic denominator bound for the selected minor
-- statement:
--   For a nonzero selected minor, find a positive integer multiplier that makes its determinant a Gaussian integer, with the logarithm of the multiplier bounded by the row-count-times-`H` arithmetic budget.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData

open scoped BigOperators

theorem OAI.PiExponent.MatrixArithmetic.selectedMinor_denominator_clear_v2
    {m K : ℕ} {w0 v0 θ F H wmin : ℝ}
    (p : Fin m → ℤ) (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i)
    (hK : 0 < K) (hw0 : 0 < w0) (hv0 : 0 < v0) (hθ : 0 < θ)
    (hF : 0 ≤ F) (hH : 0 < H) (hmin : 0 < wmin)
    (hwmin : ∀ i, wmin ≤ OAI.PiExponent.MatrixArithmetic.logWeights q i)
    (selection : OAI.PiExponent.InterpolationMatrix.Row K v0 θ
        (OAI.PiExponent.MatrixArithmetic.logWeights q) H →
      OAI.PiExponent.InterpolationMatrix.Column w0
        (OAI.PiExponent.MatrixArithmetic.logWeights q) H)
    (hdet : (OAI.PiExponent.MatrixArithmetic.selectedMinor K w0 v0 θ F H p q selection).det ≠ 0) :
    ∃ D : ℕ, 0 < D ∧
      ∃ g : GaussianInt,
        (D : ℂ) * (OAI.PiExponent.MatrixArithmetic.selectedMinor K w0 v0 θ F H p q selection).det = (g : ℂ) ∧
        Real.log (D : ℝ) ≤
          ((Fintype.card (OAI.PiExponent.InterpolationMatrix.Row K v0 θ
            (OAI.PiExponent.MatrixArithmetic.logWeights q) H) : ℝ) * H) *
            ((1 - OAI.PiExponent.MatrixArithmetic.meanRowWeight K v0 θ q H) +
              (OAI.PiExponent.Arithmetic.lcmConstant * F * m / v0 +
                OAI.PiExponent.Arithmetic.lcmConstant *
                  (∑ i, 1 / OAI.PiExponent.MatrixArithmetic.logWeights q i) + θ / wmin)) := by sorry
