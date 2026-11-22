-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_moment_tail_le
-- name    : LongGapsBetweenPrimes.moment_tail_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:32:48.392995+00:00
-- url     : https://prove2.me/theorems/9a2a9919-6694-459b-be06-6479fa57bc7f
-- title:
--   Long Gaps Between Primes: moment tail le
-- statement:
--   Rankin's tail estimate, in the finite form needed for (3.10).
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L241-L257
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L241-L257

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.moment_tail_le {α : Type*} (s : Finset α) (f v : α → ℝ) (D β : ℝ)
    (hD : 0 < D) (hβ : 0 ≤ β) (hf : ∀ a ∈ s, 0 ≤ f a)
    (hv : ∀ a ∈ s, 0 ≤ v a) :
    (∑ a ∈ s.filter (fun a => D < v a), f a) ≤
      D ^ (-β) * ∑ a ∈ s, f a * (v a) ^ β := by sorry
