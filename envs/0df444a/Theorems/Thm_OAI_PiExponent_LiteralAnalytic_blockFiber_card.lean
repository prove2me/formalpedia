-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_blockFiber_card
-- name    : OAI.PiExponent.LiteralAnalytic.blockFiber_card
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T19:00:32.516556+00:00
-- url     : https://prove2.me/theorems/a96ddf9f-80ab-4e59-a7a0-c6d0b7ada241
-- title:
--   Count a fixed block total by a binomial coefficient
-- statement:
--   The number of assignments of total n to m slots is the weak-composition coefficient. This includes m = 0: the fiber has one element for n = 0 and is empty for positive n, matching the natural-number binomial expression.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L163-L175

import Mathlib.Tactic

open scoped BigOperators

theorem OAI.PiExponent.LiteralAnalytic.blockFiber_card
    (m n : ℕ) :
    Fintype.card
      {g : Fin m → Fin (n + 1) //
        Finset.univ.sum (fun j => (g j).val) = n} =
      Nat.choose (n + m - 1) n := by sorry
