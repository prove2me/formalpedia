-- Prove2me | Theorems.Thm_OAI_PiExponent_MatrixTranslationBounds_scaled_rational_center_error
-- name    : OAI.PiExponent.MatrixTranslationBounds.scaled_rational_center_error
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T12:33:55.907756+00:00
-- url     : https://prove2.me/theorems/a188ae40-6a9a-4ec0-9a53-b8848f38c082
-- title:
--   Norm of the scaled rational-center error
-- statement:
--   For a positive denominator, the norm of the scaled complex rational-center error is bounded by twice the scale times the corresponding real approximation error.
-- source:
--   OpenAI math repository pinned commit adc7f1241b42e322a6451854ab7e4b4c146bf78a; lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean, original theorem norm_choiceScalar_le. Pinned platform Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_MatrixArithmetic_CoreData
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_LiteralAnalyticSummand_InterfaceData

open OAI.PiExponent OAI.PiExponent.MatrixArithmetic

theorem OAI.PiExponent.MatrixTranslationBounds.scaled_rational_center_error {m : ℕ}
    (p : Fin m → ℤ) (q : Fin m → ℕ) (j : ℕ) (i : Fin m)
    (hq : 1 ≤ q i) :
    ‖(j : ℂ) * (MatrixArithmetic.rationalCenters p q i - logarithmicPeriod)‖ ≤
      (2 * (j : ℝ)) * |Real.pi - (p i : ℝ) / (q i : ℝ)| := by sorry
