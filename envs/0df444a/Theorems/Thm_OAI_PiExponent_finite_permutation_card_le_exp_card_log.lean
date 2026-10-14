-- Prove2me | Theorems.Thm_OAI_PiExponent_finite_permutation_card_le_exp_card_log
-- name    : OAI.PiExponent.finite_permutation_card_le_exp_card_log
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-13T10:35:00.616085+00:00
-- url     : https://prove2.me/theorems/462adb32-90ea-4b34-bc61-883d48ce192a
-- title:
--   Finite permutation count exponential bound
-- statement:
--   Bound the cardinality of the permutation group of a finite type by the exponential of its cardinality times the logarithm of its cardinality. Applying this with the row type supplies the missing $N\log N$ term.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib.Tactic

open scoped BigOperators

theorem OAI.PiExponent.finite_permutation_card_le_exp_card_log
    {α : Type*} [Fintype α] [DecidableEq α] :
    (Fintype.card (Equiv.Perm α) : ℝ) ≤
      Real.exp ((Fintype.card α : ℝ) * Real.log (Fintype.card α : ℝ)) := by sorry
