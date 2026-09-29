-- Prove2me | Theorems.Thm_Freiman_separated_copies_exist
-- name    : Freiman.separated_copies_exist
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:53:18.929088+00:00
-- url     : https://prove2.me/theorems/b0a0e15d-4fd3-4d08-8f4e-b99bdc985b55
-- title:
--   separated copies exist
-- statement:
--   The finite windows of radii $N,N+1,\ldots$ can be concatenated in order with the digit 2 between windows, and extended by 2 on the left. This is an existence statement for the explicit SeparatedCopies relation.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.6, Theorem 1.9 (found:separated-peaks), proof by separated copies.

import Definitions.Def_Freiman_wordRealization

open Freiman

theorem Freiman.separated_copies_exist (a : ℤ → ℕ+) (N : ℕ) :
    ∃ b : ℤ → ℕ+, SeparatedCopies a b N := by sorry
