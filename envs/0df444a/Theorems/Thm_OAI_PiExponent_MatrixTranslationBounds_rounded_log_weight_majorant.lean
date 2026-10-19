-- Prove2me | Theorems.Thm_OAI_PiExponent_MatrixTranslationBounds_rounded_log_weight_majorant
-- name    : OAI.PiExponent.MatrixTranslationBounds.rounded_log_weight_majorant
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T12:51:40.948924+00:00
-- url     : https://prove2.me/theorems/07d37756-91e2-4fda-965c-ac86d9081be9
-- title:
--   Exponential majorant with rounded logarithmic weight
-- statement:
--   For positive natural q and nonnegative ν, the scaled power term is bounded by the exponential using the rounded logarithmic weight, when j ≤ K and K ≥ 1.
-- source:
--   OpenAI math repository pinned commit adc7f1241b42e322a6451854ab7e4b4c146bf78a; lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean, original theorem norm_choiceScalar_le. Pinned platform Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_MatrixArithmetic_CoreData

theorem OAI.PiExponent.MatrixTranslationBounds.rounded_log_weight_majorant
    (K j : ℕ) (ν : ℝ) (q : ℕ)
    (hK : 1 ≤ K) (hj : j ≤ K) (hν : 0 ≤ ν) (hq : 1 ≤ q) :
    (2 * (j : ℝ)) * (q : ℝ) ^ (-ν) ≤
      Real.exp ((Real.log (2 * (K : ℝ)) + ν) -
        ν * (⌈Real.log (q : ℝ)⌉₊ : ℝ)) := by sorry
