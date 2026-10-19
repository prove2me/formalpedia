-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_weakCompositionFiber_card_eq_sym
-- name    : OAI.PiExponent.LiteralAnalytic.weakCompositionFiber_card_eq_sym
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T19:04:51.520708+00:00
-- url     : https://prove2.me/theorems/2263699f-f696-44ac-aa25-8d8f40711014
-- title:
--   Count weak compositions by symmetric powers
-- statement:
--   The number of bounded functions whose values sum to `k` equals the number of multisets of size `k` drawn from the finite type.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L163-L175

import Mathlib.Data.Sym.Card
import Definitions.Def_weakCompositionFiber

open scoped BigOperators

theorem OAI.PiExponent.LiteralAnalytic.weakCompositionFiber_card_eq_sym
    (A : Type*) [Fintype A] [DecidableEq A] (k : Nat) :
    Fintype.card (OAI.PiExponent.LiteralAnalytic.weakCompositionFiber A k) =
      Fintype.card (Sym A k) := by sorry
