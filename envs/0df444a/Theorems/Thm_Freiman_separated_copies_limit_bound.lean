-- Prove2me | Theorems.Thm_Freiman_separated_copies_limit_bound
-- name    : Freiman.separated_copies_limit_bound
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:53:24.605755+00:00
-- url     : https://prove2.me/theorems/36c350b1-bea9-4ecc-a0f4-2aca53610963
-- title:
--   separated copies limit bound
-- statement:
--   Under either background hypothesis of Theorem 1.9, every coordinate limit viewed at increasing copied-word positions has central value at most $t$. Fixed shifts use the assumed global upper bound of the model; background limits use the appropriate alphabet bound.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.6, Theorem 1.9 (found:separated-peaks), proof by separated copies.

import Definitions.Def_Freiman_wordRealization

open Freiman

theorem Freiman.separated_copies_limit_bound (a b : ℤ → ℕ+) (N : ℕ) (t : ℝ)
    (hcopy : SeparatedCopies a b N)
    (hfinite : ∀ i : ℤ, N ≤ i.natAbs → (a i : ℕ) ≤ 3)
    (hmax : ∀ i : ℤ, localValue a i ≤ t)
    (hcondition : Real.sqrt 21 ≤ t ∨ (AvoidsBlock a [3, 1, 3, 1, 3] ∧ (4 * Real.sqrt 462 / 19 : ℝ) ≤ t))
    (u : ℕ → ℕ) (hu : StrictMono u) (y : ℤ → ℕ+)
    (hy : CoordinateLimit (fun j i => b ((u j : ℤ) + i)) y) :
    localValue y 0 ≤ t := by sorry
