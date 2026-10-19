-- Prove2me | Theorems.Thm_OAI_PiExponent_MatrixArithmetic_selectedMinor_arithmetic_lower_bound_v2
-- name    : OAI.PiExponent.MatrixArithmetic.selectedMinor_arithmetic_lower_bound_v2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-16T22:16:21.383086+00:00
-- url     : https://prove2.me/theorems/7435a1c1-b93a-47ff-a0b6-0f934da7d698
-- title:
--   Arithmetic lower bound for a nonzero selected minor
-- statement:
--   For admissible positive parameters and weights bounded below by `wmin`, a nonzero selected minor has normalized log norm bounded below by the negative mean-row contribution and the explicit arithmetic denominator error.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData

open scoped BigOperators

theorem OAI.PiExponent.MatrixArithmetic.selectedMinor_arithmetic_lower_bound_v2
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
    -(1 - OAI.PiExponent.MatrixArithmetic.meanRowWeight K v0 θ q H) -
      (OAI.PiExponent.Arithmetic.lcmConstant * F * m / v0 +
        OAI.PiExponent.Arithmetic.lcmConstant *
          (∑ i, 1 / OAI.PiExponent.MatrixArithmetic.logWeights q i) + θ / wmin) ≤
      Real.log ‖(OAI.PiExponent.MatrixArithmetic.selectedMinor K w0 v0 θ F H p q selection).det‖ /
        ((Fintype.card (OAI.PiExponent.InterpolationMatrix.Row K v0 θ
          (OAI.PiExponent.MatrixArithmetic.logWeights q) H) : ℝ) * H) := by sorry
