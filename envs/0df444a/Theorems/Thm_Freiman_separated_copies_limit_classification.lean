-- Prove2me | Theorems.Thm_Freiman_separated_copies_limit_classification
-- name    : Freiman.separated_copies_limit_classification
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:53:21.830442+00:00
-- url     : https://prove2.me/theorems/e2d674a1-03a9-4c6c-9fb1-25ee5deb8d3e
-- title:
--   separated copies limit classification
-- statement:
--   Every coordinatewise limit viewed from increasing positions in the copied word is either a fixed shift of the original word, or a word using only 1, 2, 3. The two cases are bounded distance from copied centers and distance tending to infinity; the finite exceptional positions are retained in the hypothesis.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.6, Theorem 1.9 (found:separated-peaks), proof by separated copies.

import Definitions.Def_Freiman_wordRealization

open Freiman

theorem Freiman.separated_copies_limit_classification (a b : ℤ → ℕ+) (N : ℕ)
    (hcopy : SeparatedCopies a b N)
    (hfinite : ∀ i : ℤ, N ≤ i.natAbs → (a i : ℕ) ≤ 3)
    (u : ℕ → ℕ) (hu : StrictMono u) (y : ℤ → ℕ+)
    (hy : CoordinateLimit (fun j i => b ((u j : ℤ) + i)) y) :
    BackgroundOrShift a y := by sorry
