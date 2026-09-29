-- Prove2me | Theorems.Thm_Freiman_finite_exception_alphabet
-- name    : Freiman.finite_exception_alphabet
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:53:12.630222+00:00
-- url     : https://prove2.me/theorems/6a5c286b-9ba1-4171-a565-2a9f4067ac80
-- title:
--   finite exception alphabet
-- statement:
--   A two-sided word whose digits outside a finite central window are at most 3 uses a finite alphabet. The finitely many remaining digit values have a common finite bound.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.6, Theorem 1.9 (found:separated-peaks), proof by separated copies.

import Definitions.Def_Freiman_wordRealization

open Freiman

theorem Freiman.finite_exception_alphabet (a : ℤ → ℕ+) (h : EventuallyThree a) :
    HasFiniteAlphabet a := by sorry
