-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_weakCompositionFiber_card
-- name    : OAI.PiExponent.LiteralAnalytic.weakCompositionFiber_card
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T18:53:23.606769+00:00
-- url     : https://prove2.me/theorems/4de87108-34d2-498b-81c3-d67062459afa
-- title:
--   Count weak compositions on a finite type
-- statement:
--   Count functions α → Fin (k + 1) whose values sum to k by stars and bars. For an empty α, both sides equal one at k = 0 and zero at positive k.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L163-L175

import Mathlib.Tactic
import Mathlib.Data.Nat.Choose.Basic
import Definitions.Def_weakCompositionFiber

open scoped BigOperators

theorem OAI.PiExponent.LiteralAnalytic.weakCompositionFiber_card
    (α : Type*) [Fintype α] [DecidableEq α] (k : ℕ) :
    Fintype.card (OAI.PiExponent.LiteralAnalytic.weakCompositionFiber α k) =
      Nat.choose (k + Fintype.card α - 1) k := by sorry
