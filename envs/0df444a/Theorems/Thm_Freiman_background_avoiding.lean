-- Prove2me | Theorems.Thm_Freiman_background_avoiding
-- name    : Freiman.background_avoiding
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:53:19.356142+00:00
-- url     : https://prove2.me/theorems/3f554b60-e3c7-4191-8e26-404c88f16a70
-- title:
--   background avoiding
-- statement:
--   Every local value of a word on $\{1,2,3\}$ avoiding 31313 is at most $c_*=4\sqrt{462}/19$.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.4, Lemma 1.7 (found:background), greatest-tail and central-neighbour case analysis.

import Definitions.Def_Freiman_wordRealization

open Freiman

theorem Freiman.background_avoiding (a : ℤ → ℕ+) (ha : ∀ i : ℤ, (a i : ℕ) ≤ 3)
    (havoid : AvoidsBlock a [3, 1, 3, 1, 3]) (i : ℤ) :
    localValue a i ≤ 4 * Real.sqrt 462 / 19 := by sorry
