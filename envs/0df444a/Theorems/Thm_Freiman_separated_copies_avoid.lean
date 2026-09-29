-- Prove2me | Theorems.Thm_Freiman_separated_copies_avoid
-- name    : Freiman.separated_copies_avoid
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:53:13.278951+00:00
-- url     : https://prove2.me/theorems/0d90c6b4-c32f-4299-ace3-a7875609b532
-- title:
--   separated copies avoid
-- statement:
--   Avoidance of 31313 is preserved by the separated-copy construction: each block avoids it, and a word crossing a join contains the separator 2.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.6, Theorem 1.9 (found:separated-peaks), proof by separated copies.

import Definitions.Def_Freiman_wordRealization

open Freiman

theorem Freiman.separated_copies_avoid (a b : ℤ → ℕ+) (N : ℕ)
    (hcopy : SeparatedCopies a b N) (ha : AvoidsBlock a [3, 1, 3, 1, 3]) :
    AvoidsBlock b [3, 1, 3, 1, 3] := by sorry
