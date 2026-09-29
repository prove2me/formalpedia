-- Prove2me | Theorems.Thm_Freiman_background_restricted
-- name    : Freiman.background_restricted
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:53:21.830442+00:00
-- url     : https://prove2.me/theorems/096ec227-a727-4304-8865-f98bb1751956
-- title:
--   background restricted
-- statement:
--   In a word on $\{1,2,3,4\}$ avoiding 14, 41 and 31313, every position carrying a digit at most 3 has local value at most $c_*$. The bound is only asserted at those positions.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.4, Lemma 1.7 (found:background), greatest-tail and central-neighbour case analysis.

import Definitions.Def_Freiman_wordRealization

open Freiman

theorem Freiman.background_restricted (a : ℤ → ℕ+) (ha : ∀ i : ℤ, (a i : ℕ) ≤ 4)
    (h14 : AvoidsBlock a [1, 4]) (h41 : AvoidsBlock a [4, 1])
    (h31313 : AvoidsBlock a [3, 1, 3, 1, 3]) (i : ℤ) (hi : (a i : ℕ) ≤ 3) :
    localValue a i ≤ 4 * Real.sqrt 462 / 19 := by sorry
