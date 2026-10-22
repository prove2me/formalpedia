-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_allocationSum_eq_weakCompositionFiber_card
-- name    : OAI.PiExponent.LiteralAnalytic.allocationSum_eq_weakCompositionFiber_card
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T18:53:07.754418+00:00
-- url     : https://prove2.me/theorems/bb712f34-efc7-4e8f-b1bd-581599fc8465
-- title:
--   Represent weighted allocations as weak compositions
-- statement:
--   The weighted allocation sum counts assignments of total k to the expanded slots Σ i, Fin (e i), grouped by their block totals. Zero exponents give empty blocks, which contribute only when their block total is zero.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L163-L175

import Mathlib.Tactic
import Definitions.Def_allocationSum
import Definitions.Def_weakCompositionFiber

open scoped BigOperators

theorem OAI.PiExponent.LiteralAnalytic.allocationSum_eq_weakCompositionFiber_card
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (e : σ → ℕ) (k : ℕ) :
    OAI.PiExponent.LiteralAnalytic.allocationSum e k =
      Fintype.card
        (OAI.PiExponent.LiteralAnalytic.weakCompositionFiber (Σ i, Fin (e i)) k) := by sorry
