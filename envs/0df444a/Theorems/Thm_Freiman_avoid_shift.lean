-- Prove2me | Theorems.Thm_Freiman_avoid_shift
-- name    : Freiman.avoid_shift
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:53:17.629467+00:00
-- url     : https://prove2.me/theorems/92df2a84-a33a-4cfa-ab2e-5093ce9ede47
-- title:
--   avoid shift
-- statement:
--   A shift of a two-sided word avoiding a finite block still avoids that block.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.6, Theorem 1.9 (found:separated-peaks), proof by separated copies.

import Definitions.Def_Freiman_wordRealization

open Freiman

theorem Freiman.avoid_shift (a : ℤ → ℕ+) (w : List ℕ) (s : ℤ) (h : AvoidsBlock a w) :
    AvoidsBlock (fun i : ℤ => a (s + i)) w := by sorry
