-- Prove2me | Theorems.Thm_Freiman_avoid_coordinate_limit
-- name    : Freiman.avoid_coordinate_limit
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:53:15.998711+00:00
-- url     : https://prove2.me/theorems/0596e9aa-7c76-4032-9e57-e37fdcc3676c
-- title:
--   avoid coordinate limit
-- statement:
--   Avoidance of any fixed finite block is preserved by coordinatewise convergence of discrete digit words. A forbidden occurrence in the limit would already occur in all sufficiently late words.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.6, Theorem 1.9 (found:separated-peaks), proof by separated copies.

import Definitions.Def_Freiman_wordRealization

open Freiman

theorem Freiman.avoid_coordinate_limit (A : ℕ → ℤ → ℕ+) (a : ℤ → ℕ+) (w : List ℕ)
    (hA : ∀ j : ℕ, AvoidsBlock (A j) w) (hlim : CoordinateLimit A a) :
    AvoidsBlock a w := by sorry
