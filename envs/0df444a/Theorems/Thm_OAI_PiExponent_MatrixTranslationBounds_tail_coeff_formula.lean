-- Prove2me | Theorems.Thm_OAI_PiExponent_MatrixTranslationBounds_tail_coeff_formula
-- name    : OAI.PiExponent.MatrixTranslationBounds.tail_coeff_formula
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T17:09:14.348631+00:00
-- url     : https://prove2.me/theorems/dd7f9db3-7a76-459d-83e6-e515c7a951c6
-- title:
--   Coefficient formula for a power series tail
-- statement:
--   The coefficient of a power series tail is zero below the truncation cutoff and is the negative of the original coefficient at or above the cutoff.
-- source:
--   OpenAI math repository pinned commit adc7f1241b42e322a6451854ab7e4b4c146bf78a; lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean, original theorem norm_choiceScalar_le. Pinned platform Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib.RingTheory.PowerSeries.Trunc
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_LiteralAnalyticSummand_InterfaceData

open OAI.PiExponent.RowTranslation

theorem OAI.PiExponent.MatrixTranslationBounds.tail_coeff_formula {R : Type*} [CommRing R] (T n : ℕ) (f : PowerSeries R) :
    PowerSeries.coeff n (OAI.PiExponent.RowTranslation.tail T f) =
      if n < T then 0 else -PowerSeries.coeff n f := by sorry
