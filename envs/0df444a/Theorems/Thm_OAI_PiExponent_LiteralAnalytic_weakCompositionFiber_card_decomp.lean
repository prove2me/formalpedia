-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_weakCompositionFiber_card_decomp
-- name    : OAI.PiExponent.LiteralAnalytic.weakCompositionFiber_card_decomp
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T19:00:17.317024+00:00
-- url     : https://prove2.me/theorems/002c24e3-4e3c-4abf-822b-cf64ca49b29d
-- title:
--   Decompose slot assignments by block totals
-- statement:
--   The cardinality of the weak-composition fiber on expanded slots is the sum, over all bounded vectors of block totals summing to k, of the product of the cardinalities of the corresponding per-block assignment fibers. The total constraint ensures each block total is at most k; vectors failing the total constraint contribute zero.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L163-L175

import Mathlib.Tactic
import Definitions.Def_weakCompositionFiber

open scoped BigOperators

theorem OAI.PiExponent.LiteralAnalytic.weakCompositionFiber_card_decomp
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (e : σ → ℕ) (k : ℕ) :
    Fintype.card
        (OAI.PiExponent.LiteralAnalytic.weakCompositionFiber (Σ i, Fin (e i)) k) =
      ∑ n : σ → Fin (k + 1),
        (if ∑ i, (n i).val = k then
          ∏ i,
            Fintype.card
              {g : Fin (e i) → Fin ((n i).val + 1) //
                Finset.univ.sum (fun j => (g j).val) = (n i).val}
         else 0) := by sorry
