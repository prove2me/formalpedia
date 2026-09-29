-- Prove2me | Theorems.Thm_Freiman_separated_copies_alphabet
-- name    : Freiman.separated_copies_alphabet
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:53:14.74963+00:00
-- url     : https://prove2.me/theorems/2d246055-3df4-400d-b307-60669217306f
-- title:
--   separated copies alphabet
-- statement:
--   The separated copied word uses only digits of the original word and the separator 2, hence has a finite alphabet whenever the original does.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.6, Theorem 1.9 (found:separated-peaks), proof by separated copies.

import Definitions.Def_Freiman_wordRealization

open Freiman

theorem Freiman.separated_copies_alphabet (a b : ℤ → ℕ+) (N : ℕ) (hcopy : SeparatedCopies a b N) (ha : HasFiniteAlphabet a) :
    HasFiniteAlphabet b := by sorry
