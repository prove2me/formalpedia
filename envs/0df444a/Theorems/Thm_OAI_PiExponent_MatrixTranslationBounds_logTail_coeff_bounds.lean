-- Prove2me | Theorems.Thm_OAI_PiExponent_MatrixTranslationBounds_logTail_coeff_bounds
-- name    : OAI.PiExponent.MatrixTranslationBounds.logTail_coeff_bounds
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T16:58:37.291994+00:00
-- url     : https://prove2.me/theorems/418168b4-3531-4d53-bde0-3c86ad59e9d8
-- title:
--   Coefficient bounds for tails of the formal logarithm
-- statement:
--   For every natural cutoff, the formal logarithm tail has zero constant coefficient and every coefficient has complex norm at most one. The cutoff retains degrees strictly below T, so the tail coefficients vanish below T and equal the negatives of the logarithm coefficients at and above T.
-- source:
--   OpenAI math repository pinned commit adc7f1241b42e322a6451854ab7e4b4c146bf78a; lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean, original theorem norm_choiceScalar_le. Pinned platform Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.PowerSeries.Log
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_LiteralAnalyticSummand_InterfaceData

open scoped BigOperators
open OAI.PiExponent.RowTranslation

theorem OAI.PiExponent.MatrixTranslationBounds.logTail_coeff_bounds (T : ℕ) :
    PowerSeries.coeff 0 (tail T (PowerSeries.log ℂ)) = 0 ∧
      ∀ n, ‖PowerSeries.coeff n (tail T (PowerSeries.log ℂ))‖ ≤ (1 : ℝ) := by sorry
